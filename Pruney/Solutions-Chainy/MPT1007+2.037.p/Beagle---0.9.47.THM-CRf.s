%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:16 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :   64 (  79 expanded)
%              Number of leaves         :   37 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 136 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_101,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_105,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_101])).

tff(c_106,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_110,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_106])).

tff(c_32,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_203,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_207,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_203])).

tff(c_10332,plain,(
    ! [B_5069,A_5070,C_5071] :
      ( k1_xboole_0 = B_5069
      | k1_relset_1(A_5070,B_5069,C_5071) = A_5070
      | ~ v1_funct_2(C_5071,A_5070,B_5069)
      | ~ m1_subset_1(C_5071,k1_zfmisc_1(k2_zfmisc_1(A_5070,B_5069))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10347,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_10332])).

tff(c_10350,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_207,c_10347])).

tff(c_10351,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_10350])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [D_32,B_33] : r2_hidden(D_32,k2_tarski(D_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_74])).

tff(c_10399,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10351,c_77])).

tff(c_264,plain,(
    ! [B_88,A_89] :
      ( r2_hidden(k1_funct_1(B_88,A_89),k2_relat_1(B_88))
      | ~ r2_hidden(A_89,k1_relat_1(B_88))
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14370,plain,(
    ! [B_14031,A_14032,B_14033] :
      ( r2_hidden(k1_funct_1(B_14031,A_14032),B_14033)
      | ~ r1_tarski(k2_relat_1(B_14031),B_14033)
      | ~ r2_hidden(A_14032,k1_relat_1(B_14031))
      | ~ v1_funct_1(B_14031)
      | ~ v1_relat_1(B_14031) ) ),
    inference(resolution,[status(thm)],[c_264,c_2])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14387,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_14370,c_56])).

tff(c_14404,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_64,c_10399,c_14387])).

tff(c_14409,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_14404])).

tff(c_14413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_110,c_14409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:03:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.37/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.51  
% 7.37/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.37/2.51  
% 7.37/2.51  %Foreground sorts:
% 7.37/2.51  
% 7.37/2.51  
% 7.37/2.51  %Background operators:
% 7.37/2.51  
% 7.37/2.51  
% 7.37/2.51  %Foreground operators:
% 7.37/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.37/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.37/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.37/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.37/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.37/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.37/2.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.37/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.37/2.51  tff('#skF_5', type, '#skF_5': $i).
% 7.37/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.37/2.51  tff('#skF_6', type, '#skF_6': $i).
% 7.37/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.37/2.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.37/2.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.37/2.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.37/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.37/2.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.37/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.37/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.37/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.37/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.37/2.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.37/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.37/2.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.37/2.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.37/2.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.37/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.37/2.51  
% 7.37/2.52  tff(f_103, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 7.37/2.52  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.37/2.52  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.37/2.52  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.37/2.52  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.37/2.52  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.37/2.52  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.37/2.52  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 7.37/2.52  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 7.37/2.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.37/2.52  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.37/2.52  tff(c_101, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.37/2.52  tff(c_105, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_101])).
% 7.37/2.52  tff(c_106, plain, (![C_47, B_48, A_49]: (v5_relat_1(C_47, B_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.37/2.52  tff(c_110, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_106])).
% 7.37/2.52  tff(c_32, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.37/2.52  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.37/2.52  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.37/2.53  tff(c_62, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.37/2.53  tff(c_203, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.37/2.53  tff(c_207, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_203])).
% 7.37/2.53  tff(c_10332, plain, (![B_5069, A_5070, C_5071]: (k1_xboole_0=B_5069 | k1_relset_1(A_5070, B_5069, C_5071)=A_5070 | ~v1_funct_2(C_5071, A_5070, B_5069) | ~m1_subset_1(C_5071, k1_zfmisc_1(k2_zfmisc_1(A_5070, B_5069))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.37/2.53  tff(c_10347, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_60, c_10332])).
% 7.37/2.53  tff(c_10350, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_207, c_10347])).
% 7.37/2.53  tff(c_10351, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_10350])).
% 7.37/2.53  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.37/2.53  tff(c_74, plain, (![D_32, B_33]: (r2_hidden(D_32, k2_tarski(D_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.37/2.53  tff(c_77, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_74])).
% 7.37/2.53  tff(c_10399, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10351, c_77])).
% 7.37/2.53  tff(c_264, plain, (![B_88, A_89]: (r2_hidden(k1_funct_1(B_88, A_89), k2_relat_1(B_88)) | ~r2_hidden(A_89, k1_relat_1(B_88)) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.37/2.53  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.37/2.53  tff(c_14370, plain, (![B_14031, A_14032, B_14033]: (r2_hidden(k1_funct_1(B_14031, A_14032), B_14033) | ~r1_tarski(k2_relat_1(B_14031), B_14033) | ~r2_hidden(A_14032, k1_relat_1(B_14031)) | ~v1_funct_1(B_14031) | ~v1_relat_1(B_14031))), inference(resolution, [status(thm)], [c_264, c_2])).
% 7.37/2.53  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.37/2.53  tff(c_14387, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_14370, c_56])).
% 7.37/2.53  tff(c_14404, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_64, c_10399, c_14387])).
% 7.37/2.53  tff(c_14409, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_14404])).
% 7.37/2.53  tff(c_14413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_110, c_14409])).
% 7.37/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.53  
% 7.37/2.53  Inference rules
% 7.37/2.53  ----------------------
% 7.37/2.53  #Ref     : 0
% 7.37/2.53  #Sup     : 2093
% 7.37/2.53  #Fact    : 11
% 7.37/2.53  #Define  : 0
% 7.37/2.53  #Split   : 7
% 7.37/2.53  #Chain   : 0
% 7.37/2.53  #Close   : 0
% 7.37/2.53  
% 7.37/2.53  Ordering : KBO
% 7.37/2.53  
% 7.37/2.53  Simplification rules
% 7.37/2.53  ----------------------
% 7.37/2.53  #Subsume      : 357
% 7.37/2.53  #Demod        : 261
% 7.37/2.53  #Tautology    : 224
% 7.37/2.53  #SimpNegUnit  : 63
% 7.37/2.53  #BackRed      : 4
% 7.37/2.53  
% 7.37/2.53  #Partial instantiations: 8776
% 7.37/2.53  #Strategies tried      : 1
% 7.37/2.53  
% 7.37/2.53  Timing (in seconds)
% 7.37/2.53  ----------------------
% 7.37/2.53  Preprocessing        : 0.32
% 7.37/2.53  Parsing              : 0.17
% 7.37/2.53  CNF conversion       : 0.02
% 7.37/2.53  Main loop            : 1.44
% 7.37/2.53  Inferencing          : 0.62
% 7.37/2.53  Reduction            : 0.32
% 7.37/2.53  Demodulation         : 0.22
% 7.37/2.53  BG Simplification    : 0.08
% 7.37/2.53  Subsumption          : 0.32
% 7.37/2.53  Abstraction          : 0.08
% 7.37/2.53  MUC search           : 0.00
% 7.37/2.53  Cooper               : 0.00
% 7.37/2.53  Total                : 1.80
% 7.37/2.53  Index Insertion      : 0.00
% 7.37/2.53  Index Deletion       : 0.00
% 7.37/2.53  Index Matching       : 0.00
% 7.37/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
