%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:16 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 169 expanded)
%              Number of leaves         :   37 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 288 expanded)
%              Number of equality atoms :   31 (  90 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_87,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_26,plain,(
    ! [A_17] :
      ( k7_relat_1(A_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_26])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_24])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_99])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_18] : k7_relat_1(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_147,plain,(
    ! [B_51,A_52] :
      ( k3_xboole_0(k1_relat_1(B_51),A_52) = k1_relat_1(k7_relat_1(B_51,A_52))
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_166,plain,(
    ! [A_52] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_52)) = k3_xboole_0(k1_xboole_0,A_52)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_147])).

tff(c_170,plain,(
    ! [A_52] : k3_xboole_0(k1_xboole_0,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_32,c_28,c_166])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_171,plain,(
    ! [A_53] : k3_xboole_0(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_32,c_28,c_166])).

tff(c_8,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_183,plain,(
    ! [A_53,C_7] :
      ( ~ r1_xboole_0(k1_xboole_0,A_53)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_8])).

tff(c_190,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | k3_xboole_0(A_13,k1_tarski(B_14)) != k1_tarski(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_180,plain,(
    ! [B_14] :
      ( r2_hidden(B_14,k1_xboole_0)
      | k1_tarski(B_14) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_22])).

tff(c_191,plain,(
    ! [B_14] : k1_tarski(B_14) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_180])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_276,plain,(
    ! [D_70,C_71,B_72,A_73] :
      ( r2_hidden(k1_funct_1(D_70,C_71),B_72)
      | k1_xboole_0 = B_72
      | ~ r2_hidden(C_71,A_73)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72)))
      | ~ v1_funct_2(D_70,A_73,B_72)
      | ~ v1_funct_1(D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_345,plain,(
    ! [D_81,B_82] :
      ( r2_hidden(k1_funct_1(D_81,'#skF_6'),B_82)
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_82)))
      | ~ v1_funct_2(D_81,'#skF_4',B_82)
      | ~ v1_funct_1(D_81) ) ),
    inference(resolution,[status(thm)],[c_42,c_276])).

tff(c_348,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_345])).

tff(c_351,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_348])).

tff(c_352,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_6'),k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_351])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_357,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_352,c_10])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_357])).

tff(c_364,plain,(
    ! [A_83] : ~ r1_xboole_0(k1_xboole_0,A_83) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_368,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_364])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.19/1.29  
% 2.19/1.29  %Foreground sorts:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Background operators:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Foreground operators:
% 2.19/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.19/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.19/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.29  
% 2.19/1.30  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.19/1.30  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.19/1.30  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 2.19/1.30  tff(f_58, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.19/1.30  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.19/1.30  tff(f_64, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.19/1.30  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.19/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.19/1.30  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.19/1.30  tff(f_54, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.19/1.30  tff(f_87, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.19/1.30  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.19/1.30  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.19/1.30  tff(c_87, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.19/1.30  tff(c_91, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_87])).
% 2.19/1.30  tff(c_26, plain, (![A_17]: (k7_relat_1(A_17, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.30  tff(c_95, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_26])).
% 2.19/1.30  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.30  tff(c_99, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_95, c_24])).
% 2.19/1.30  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_99])).
% 2.19/1.30  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.19/1.30  tff(c_28, plain, (![A_18]: (k7_relat_1(k1_xboole_0, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.30  tff(c_147, plain, (![B_51, A_52]: (k3_xboole_0(k1_relat_1(B_51), A_52)=k1_relat_1(k7_relat_1(B_51, A_52)) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.30  tff(c_166, plain, (![A_52]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_52))=k3_xboole_0(k1_xboole_0, A_52) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_147])).
% 2.19/1.30  tff(c_170, plain, (![A_52]: (k3_xboole_0(k1_xboole_0, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_32, c_28, c_166])).
% 2.19/1.30  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.30  tff(c_40, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.19/1.30  tff(c_171, plain, (![A_53]: (k3_xboole_0(k1_xboole_0, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_32, c_28, c_166])).
% 2.19/1.30  tff(c_8, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.30  tff(c_183, plain, (![A_53, C_7]: (~r1_xboole_0(k1_xboole_0, A_53) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_8])).
% 2.19/1.30  tff(c_190, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_183])).
% 2.19/1.30  tff(c_22, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | k3_xboole_0(A_13, k1_tarski(B_14))!=k1_tarski(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.30  tff(c_180, plain, (![B_14]: (r2_hidden(B_14, k1_xboole_0) | k1_tarski(B_14)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_171, c_22])).
% 2.19/1.30  tff(c_191, plain, (![B_14]: (k1_tarski(B_14)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_190, c_180])).
% 2.19/1.30  tff(c_48, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.19/1.30  tff(c_46, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.19/1.30  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.19/1.30  tff(c_276, plain, (![D_70, C_71, B_72, A_73]: (r2_hidden(k1_funct_1(D_70, C_71), B_72) | k1_xboole_0=B_72 | ~r2_hidden(C_71, A_73) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))) | ~v1_funct_2(D_70, A_73, B_72) | ~v1_funct_1(D_70))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.19/1.30  tff(c_345, plain, (![D_81, B_82]: (r2_hidden(k1_funct_1(D_81, '#skF_6'), B_82) | k1_xboole_0=B_82 | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_82))) | ~v1_funct_2(D_81, '#skF_4', B_82) | ~v1_funct_1(D_81))), inference(resolution, [status(thm)], [c_42, c_276])).
% 2.19/1.30  tff(c_348, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_345])).
% 2.19/1.30  tff(c_351, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5')) | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_348])).
% 2.19/1.30  tff(c_352, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_191, c_351])).
% 2.19/1.30  tff(c_10, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.30  tff(c_357, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_352, c_10])).
% 2.19/1.30  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_357])).
% 2.19/1.30  tff(c_364, plain, (![A_83]: (~r1_xboole_0(k1_xboole_0, A_83))), inference(splitRight, [status(thm)], [c_183])).
% 2.19/1.30  tff(c_368, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_364])).
% 2.19/1.30  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_368])).
% 2.19/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  Inference rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Ref     : 0
% 2.19/1.30  #Sup     : 70
% 2.19/1.30  #Fact    : 0
% 2.19/1.30  #Define  : 0
% 2.19/1.30  #Split   : 1
% 2.19/1.30  #Chain   : 0
% 2.19/1.30  #Close   : 0
% 2.19/1.30  
% 2.19/1.30  Ordering : KBO
% 2.19/1.30  
% 2.19/1.30  Simplification rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Subsume      : 9
% 2.19/1.30  #Demod        : 32
% 2.19/1.30  #Tautology    : 35
% 2.19/1.30  #SimpNegUnit  : 9
% 2.19/1.30  #BackRed      : 1
% 2.19/1.30  
% 2.19/1.30  #Partial instantiations: 0
% 2.19/1.30  #Strategies tried      : 1
% 2.19/1.30  
% 2.19/1.30  Timing (in seconds)
% 2.19/1.30  ----------------------
% 2.19/1.30  Preprocessing        : 0.32
% 2.19/1.30  Parsing              : 0.17
% 2.19/1.30  CNF conversion       : 0.02
% 2.19/1.30  Main loop            : 0.23
% 2.19/1.31  Inferencing          : 0.09
% 2.19/1.31  Reduction            : 0.07
% 2.19/1.31  Demodulation         : 0.05
% 2.19/1.31  BG Simplification    : 0.02
% 2.19/1.31  Subsumption          : 0.04
% 2.19/1.31  Abstraction          : 0.02
% 2.19/1.31  MUC search           : 0.00
% 2.19/1.31  Cooper               : 0.00
% 2.19/1.31  Total                : 0.58
% 2.19/1.31  Index Insertion      : 0.00
% 2.19/1.31  Index Deletion       : 0.00
% 2.19/1.31  Index Matching       : 0.00
% 2.19/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
