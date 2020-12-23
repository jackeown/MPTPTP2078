%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:23 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 204 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  103 ( 338 expanded)
%              Number of equality atoms :   67 ( 259 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_72,axiom,(
    ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(c_52,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_95,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k2_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_104,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_95])).

tff(c_110,plain,
    ( k3_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50,c_104])).

tff(c_111,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_110])).

tff(c_4,plain,(
    ! [A_2,B_3] : k2_xboole_0(A_2,k3_xboole_0(A_2,B_3)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [A_43,C_44,B_45] :
      ( k1_tarski(A_43) = C_44
      | k1_xboole_0 = C_44
      | k2_xboole_0(B_45,C_44) != k1_tarski(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_121,plain,(
    ! [A_2,B_3,A_43] :
      ( k3_xboole_0(A_2,B_3) = k1_tarski(A_43)
      | k3_xboole_0(A_2,B_3) = k1_xboole_0
      | k1_tarski(A_43) != A_2 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_115])).

tff(c_181,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(k1_tarski(A_67),B_68) = k1_tarski(A_67)
      | k3_xboole_0(k1_tarski(A_67),B_68) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_121])).

tff(c_299,plain,(
    ! [A_79,B_80] :
      ( k2_xboole_0(k1_tarski(A_79),k1_tarski(A_79)) = k1_tarski(A_79)
      | k3_xboole_0(k1_tarski(A_79),B_80) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_4])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | k3_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) != k1_tarski(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4404,plain,(
    ! [B_81] :
      ( k1_xboole_0 = B_81
      | k1_tarski(k1_xboole_0) != k1_xboole_0
      | k2_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_18])).

tff(c_46,plain,(
    ! [A_22,B_23,C_24,D_25] : v1_relat_1(k2_tarski(k4_tarski(A_22,B_23),k4_tarski(C_24,D_25))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4406,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_tarski(k1_xboole_0) != k1_xboole_0
    | k2_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4404,c_46])).

tff(c_5873,plain,
    ( k1_tarski(k1_xboole_0) != k1_xboole_0
    | k2_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_4406])).

tff(c_5915,plain,(
    k1_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5873])).

tff(c_40,plain,(
    ! [A_17] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_143,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_3'(A_53,B_54),B_54)
      | k1_xboole_0 = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6930,plain,(
    ! [A_1566,A_1567] :
      ( '#skF_3'(A_1566,k1_tarski(A_1567)) = A_1567
      | k1_tarski(A_1567) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(A_1567),k1_zfmisc_1(A_1566)) ) ),
    inference(resolution,[status(thm)],[c_143,c_6])).

tff(c_7047,plain,(
    ! [A_17] :
      ( '#skF_3'(k1_zfmisc_1(A_17),k1_tarski(k1_xboole_0)) = k1_xboole_0
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_6930])).

tff(c_7051,plain,(
    ! [A_1606] : '#skF_3'(k1_zfmisc_1(A_1606),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5915,c_7047])).

tff(c_38,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1('#skF_3'(A_14,B_15),A_14)
      | k1_xboole_0 = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7059,plain,(
    ! [A_1606] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1606))
      | k1_tarski(k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_1606))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7051,c_38])).

tff(c_7400,plain,(
    ! [A_1606] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1606))
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7059])).

tff(c_7417,plain,(
    ! [A_1645] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1645)) ),
    inference(negUnitSimplification,[status(thm)],[c_5915,c_7400])).

tff(c_42,plain,(
    ! [B_20,A_18] :
      ( v1_relat_1(B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7420,plain,(
    ! [A_1645] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1645) ) ),
    inference(resolution,[status(thm)],[c_7417,c_42])).

tff(c_7563,plain,(
    ! [A_1645] : ~ v1_relat_1(A_1645) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_7420])).

tff(c_7923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7563,c_46])).

tff(c_7925,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5873])).

tff(c_169,plain,(
    ! [A_43,B_3] :
      ( k3_xboole_0(k1_tarski(A_43),B_3) = k1_tarski(A_43)
      | k3_xboole_0(k1_tarski(A_43),B_3) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_121])).

tff(c_198,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(k1_tarski(A_69),B_70) = k1_xboole_0
      | k1_tarski(A_69) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_169])).

tff(c_208,plain,(
    ! [B_10,A_69] :
      ( B_10 = A_69
      | k1_tarski(A_69) != k1_xboole_0
      | k1_tarski(A_69) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_18])).

tff(c_7950,plain,(
    ! [B_10] :
      ( k1_xboole_0 = B_10
      | k1_tarski(k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7925,c_208])).

tff(c_8114,plain,(
    ! [B_1762] : k1_xboole_0 = B_1762 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7925,c_7950])).

tff(c_8159,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8114,c_46])).

tff(c_8204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_8159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.51/2.15  
% 5.51/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.15  %$ r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 5.85/2.15  
% 5.85/2.15  %Foreground sorts:
% 5.85/2.15  
% 5.85/2.15  
% 5.85/2.15  %Background operators:
% 5.85/2.15  
% 5.85/2.15  
% 5.85/2.15  %Foreground operators:
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.85/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.85/2.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.85/2.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.85/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.85/2.15  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 5.85/2.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.85/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.85/2.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.85/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.85/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.85/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.85/2.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.85/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.85/2.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.85/2.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.85/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.85/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.85/2.15  
% 5.85/2.16  tff(f_90, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 5.85/2.16  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.85/2.16  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.85/2.16  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 5.85/2.16  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.85/2.16  tff(f_58, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.85/2.16  tff(f_40, axiom, (![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 5.85/2.16  tff(f_85, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 5.85/2.16  tff(f_72, axiom, (![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 5.85/2.16  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 5.85/2.16  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.85/2.16  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.85/2.16  tff(c_52, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.85/2.16  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.85/2.16  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.85/2.16  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.85/2.16  tff(c_95, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k2_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.85/2.16  tff(c_104, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_95])).
% 5.85/2.16  tff(c_110, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50, c_104])).
% 5.85/2.16  tff(c_111, plain, (~v1_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_110])).
% 5.85/2.16  tff(c_4, plain, (![A_2, B_3]: (k2_xboole_0(A_2, k3_xboole_0(A_2, B_3))=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.85/2.16  tff(c_115, plain, (![A_43, C_44, B_45]: (k1_tarski(A_43)=C_44 | k1_xboole_0=C_44 | k2_xboole_0(B_45, C_44)!=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.85/2.16  tff(c_121, plain, (![A_2, B_3, A_43]: (k3_xboole_0(A_2, B_3)=k1_tarski(A_43) | k3_xboole_0(A_2, B_3)=k1_xboole_0 | k1_tarski(A_43)!=A_2)), inference(superposition, [status(thm), theory('equality')], [c_4, c_115])).
% 5.85/2.16  tff(c_181, plain, (![A_67, B_68]: (k3_xboole_0(k1_tarski(A_67), B_68)=k1_tarski(A_67) | k3_xboole_0(k1_tarski(A_67), B_68)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_121])).
% 5.85/2.16  tff(c_299, plain, (![A_79, B_80]: (k2_xboole_0(k1_tarski(A_79), k1_tarski(A_79))=k1_tarski(A_79) | k3_xboole_0(k1_tarski(A_79), B_80)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_181, c_4])).
% 5.85/2.16  tff(c_18, plain, (![B_10, A_9]: (B_10=A_9 | k3_xboole_0(k1_tarski(A_9), k1_tarski(B_10))!=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.85/2.16  tff(c_4404, plain, (![B_81]: (k1_xboole_0=B_81 | k1_tarski(k1_xboole_0)!=k1_xboole_0 | k2_xboole_0(k1_tarski(k1_xboole_0), k1_tarski(k1_xboole_0))=k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_299, c_18])).
% 5.85/2.16  tff(c_46, plain, (![A_22, B_23, C_24, D_25]: (v1_relat_1(k2_tarski(k4_tarski(A_22, B_23), k4_tarski(C_24, D_25))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.85/2.16  tff(c_4406, plain, (v1_relat_1(k1_xboole_0) | k1_tarski(k1_xboole_0)!=k1_xboole_0 | k2_xboole_0(k1_tarski(k1_xboole_0), k1_tarski(k1_xboole_0))=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4404, c_46])).
% 5.85/2.16  tff(c_5873, plain, (k1_tarski(k1_xboole_0)!=k1_xboole_0 | k2_xboole_0(k1_tarski(k1_xboole_0), k1_tarski(k1_xboole_0))=k1_tarski(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_111, c_4406])).
% 5.85/2.16  tff(c_5915, plain, (k1_tarski(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5873])).
% 5.85/2.16  tff(c_40, plain, (![A_17]: (m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.85/2.16  tff(c_143, plain, (![A_53, B_54]: (r2_hidden('#skF_3'(A_53, B_54), B_54) | k1_xboole_0=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.16  tff(c_6, plain, (![C_8, A_4]: (C_8=A_4 | ~r2_hidden(C_8, k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.85/2.16  tff(c_6930, plain, (![A_1566, A_1567]: ('#skF_3'(A_1566, k1_tarski(A_1567))=A_1567 | k1_tarski(A_1567)=k1_xboole_0 | ~m1_subset_1(k1_tarski(A_1567), k1_zfmisc_1(A_1566)))), inference(resolution, [status(thm)], [c_143, c_6])).
% 5.85/2.16  tff(c_7047, plain, (![A_17]: ('#skF_3'(k1_zfmisc_1(A_17), k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_6930])).
% 5.85/2.16  tff(c_7051, plain, (![A_1606]: ('#skF_3'(k1_zfmisc_1(A_1606), k1_tarski(k1_xboole_0))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_5915, c_7047])).
% 5.85/2.16  tff(c_38, plain, (![A_14, B_15]: (m1_subset_1('#skF_3'(A_14, B_15), A_14) | k1_xboole_0=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.16  tff(c_7059, plain, (![A_1606]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1606)) | k1_tarski(k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_1606))))), inference(superposition, [status(thm), theory('equality')], [c_7051, c_38])).
% 5.85/2.16  tff(c_7400, plain, (![A_1606]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1606)) | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7059])).
% 5.85/2.16  tff(c_7417, plain, (![A_1645]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1645)))), inference(negUnitSimplification, [status(thm)], [c_5915, c_7400])).
% 5.85/2.16  tff(c_42, plain, (![B_20, A_18]: (v1_relat_1(B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.85/2.16  tff(c_7420, plain, (![A_1645]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1645))), inference(resolution, [status(thm)], [c_7417, c_42])).
% 5.85/2.16  tff(c_7563, plain, (![A_1645]: (~v1_relat_1(A_1645))), inference(negUnitSimplification, [status(thm)], [c_111, c_7420])).
% 5.85/2.16  tff(c_7923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7563, c_46])).
% 5.85/2.16  tff(c_7925, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_5873])).
% 5.85/2.16  tff(c_169, plain, (![A_43, B_3]: (k3_xboole_0(k1_tarski(A_43), B_3)=k1_tarski(A_43) | k3_xboole_0(k1_tarski(A_43), B_3)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_121])).
% 5.85/2.16  tff(c_198, plain, (![A_69, B_70]: (k3_xboole_0(k1_tarski(A_69), B_70)=k1_xboole_0 | k1_tarski(A_69)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_169])).
% 5.85/2.16  tff(c_208, plain, (![B_10, A_69]: (B_10=A_69 | k1_tarski(A_69)!=k1_xboole_0 | k1_tarski(A_69)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_198, c_18])).
% 5.85/2.16  tff(c_7950, plain, (![B_10]: (k1_xboole_0=B_10 | k1_tarski(k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7925, c_208])).
% 5.85/2.16  tff(c_8114, plain, (![B_1762]: (k1_xboole_0=B_1762)), inference(demodulation, [status(thm), theory('equality')], [c_7925, c_7950])).
% 5.85/2.16  tff(c_8159, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8114, c_46])).
% 5.85/2.16  tff(c_8204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_8159])).
% 5.85/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.16  
% 5.85/2.16  Inference rules
% 5.85/2.16  ----------------------
% 5.85/2.16  #Ref     : 1
% 5.85/2.16  #Sup     : 1437
% 5.85/2.16  #Fact    : 2
% 5.85/2.16  #Define  : 0
% 5.85/2.16  #Split   : 2
% 5.85/2.16  #Chain   : 0
% 5.85/2.16  #Close   : 0
% 5.85/2.16  
% 5.85/2.16  Ordering : KBO
% 5.85/2.16  
% 5.85/2.16  Simplification rules
% 5.85/2.16  ----------------------
% 5.85/2.16  #Subsume      : 479
% 5.85/2.16  #Demod        : 289
% 5.85/2.16  #Tautology    : 92
% 5.85/2.16  #SimpNegUnit  : 12
% 5.85/2.16  #BackRed      : 2
% 5.85/2.16  
% 5.85/2.16  #Partial instantiations: 1144
% 5.85/2.16  #Strategies tried      : 1
% 5.85/2.16  
% 5.85/2.16  Timing (in seconds)
% 5.85/2.16  ----------------------
% 5.85/2.17  Preprocessing        : 0.30
% 5.85/2.17  Parsing              : 0.16
% 5.85/2.17  CNF conversion       : 0.02
% 5.85/2.17  Main loop            : 1.10
% 5.85/2.17  Inferencing          : 0.36
% 5.85/2.17  Reduction            : 0.28
% 5.85/2.17  Demodulation         : 0.20
% 5.85/2.17  BG Simplification    : 0.06
% 5.85/2.17  Subsumption          : 0.34
% 5.85/2.17  Abstraction          : 0.07
% 5.85/2.17  MUC search           : 0.00
% 5.85/2.17  Cooper               : 0.00
% 5.85/2.17  Total                : 1.43
% 5.85/2.17  Index Insertion      : 0.00
% 5.85/2.17  Index Deletion       : 0.00
% 5.85/2.17  Index Matching       : 0.00
% 5.85/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
