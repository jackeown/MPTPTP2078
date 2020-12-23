%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:28 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 149 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 242 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_52])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [A_55,B_56] :
      ( k5_relat_1(k6_relat_1(A_55),B_56) = k7_relat_1(B_56,A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k5_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    ! [B_56,A_55] :
      ( v1_relat_1(k7_relat_1(B_56,A_55))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k6_relat_1(A_55))
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_20])).

tff(c_83,plain,(
    ! [B_56,A_55] :
      ( v1_relat_1(k7_relat_1(B_56,A_55))
      | ~ v1_relat_1(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_97,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_63,B_64)),k2_relat_1(B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_102,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_21,A_20)),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_97])).

tff(c_105,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_21,A_20)),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_102])).

tff(c_133,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_137,plain,(
    k2_relset_1('#skF_3','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_133])).

tff(c_192,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1(k2_relset_1(A_84,B_85,C_86),k1_zfmisc_1(B_85))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_206,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_192])).

tff(c_211,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_206])).

tff(c_16,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(A_49,B_50)
      | v1_xboole_0(B_50)
      | ~ m1_subset_1(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [A_49,A_4] :
      ( r1_tarski(A_49,A_4)
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_49,k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_64,plain,(
    ! [A_49,A_4] :
      ( r1_tarski(A_49,A_4)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(A_4)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_61])).

tff(c_215,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_64])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_229,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,'#skF_5')
      | ~ r1_tarski(A_88,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_215,c_2])).

tff(c_237,plain,(
    ! [A_20] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_6',A_20)),'#skF_5')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_105,c_229])).

tff(c_249,plain,(
    ! [A_20] : r1_tarski(k2_relat_1(k7_relat_1('#skF_6',A_20)),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_237])).

tff(c_520,plain,(
    ! [C_127,A_128,B_129] :
      ( m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ r1_tarski(k2_relat_1(C_127),B_129)
      | ~ r1_tarski(k1_relat_1(C_127),A_128)
      | ~ v1_relat_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_373,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k5_relset_1(A_107,B_108,C_109,D_110) = k7_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_380,plain,(
    ! [D_110] : k5_relset_1('#skF_3','#skF_5','#skF_6',D_110) = k7_relat_1('#skF_6',D_110) ),
    inference(resolution,[status(thm)],[c_42,c_373])).

tff(c_40,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_3','#skF_5','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_381,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_40])).

tff(c_523,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_4')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_520,c_381])).

tff(c_539,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_523])).

tff(c_545,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_6','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_539])).

tff(c_548,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_83,c_545])).

tff(c_552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_548])).

tff(c_553,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_539])).

tff(c_557,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_553])).

tff(c_561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.44  
% 3.06/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.06/1.44  
% 3.06/1.44  %Foreground sorts:
% 3.06/1.44  
% 3.06/1.44  
% 3.06/1.44  %Background operators:
% 3.06/1.44  
% 3.06/1.44  
% 3.06/1.44  %Foreground operators:
% 3.06/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.06/1.44  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.06/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.06/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.06/1.44  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.44  tff('#skF_6', type, '#skF_6': $i).
% 3.06/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.06/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.44  
% 3.06/1.46  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 3.06/1.46  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.06/1.46  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.06/1.46  tff(f_55, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.06/1.46  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.06/1.46  tff(f_53, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.06/1.46  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.06/1.46  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.06/1.46  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.06/1.46  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.06/1.46  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.06/1.46  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.06/1.46  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.06/1.46  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.06/1.46  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.06/1.46  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.06/1.46  tff(c_52, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.06/1.46  tff(c_56, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_52])).
% 3.06/1.46  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.46  tff(c_22, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.46  tff(c_71, plain, (![A_55, B_56]: (k5_relat_1(k6_relat_1(A_55), B_56)=k7_relat_1(B_56, A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.06/1.46  tff(c_20, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.06/1.46  tff(c_77, plain, (![B_56, A_55]: (v1_relat_1(k7_relat_1(B_56, A_55)) | ~v1_relat_1(B_56) | ~v1_relat_1(k6_relat_1(A_55)) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_71, c_20])).
% 3.06/1.46  tff(c_83, plain, (![B_56, A_55]: (v1_relat_1(k7_relat_1(B_56, A_55)) | ~v1_relat_1(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_77])).
% 3.06/1.46  tff(c_28, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.06/1.46  tff(c_97, plain, (![A_63, B_64]: (r1_tarski(k2_relat_1(k5_relat_1(A_63, B_64)), k2_relat_1(B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.46  tff(c_102, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(k7_relat_1(B_21, A_20)), k2_relat_1(B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_28, c_97])).
% 3.06/1.46  tff(c_105, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(k7_relat_1(B_21, A_20)), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_102])).
% 3.06/1.46  tff(c_133, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.06/1.46  tff(c_137, plain, (k2_relset_1('#skF_3', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_133])).
% 3.06/1.46  tff(c_192, plain, (![A_84, B_85, C_86]: (m1_subset_1(k2_relset_1(A_84, B_85, C_86), k1_zfmisc_1(B_85)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.06/1.46  tff(c_206, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_137, c_192])).
% 3.06/1.46  tff(c_211, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_206])).
% 3.06/1.46  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.46  tff(c_57, plain, (![A_49, B_50]: (r2_hidden(A_49, B_50) | v1_xboole_0(B_50) | ~m1_subset_1(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.46  tff(c_4, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.06/1.46  tff(c_61, plain, (![A_49, A_4]: (r1_tarski(A_49, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_49, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_57, c_4])).
% 3.06/1.46  tff(c_64, plain, (![A_49, A_4]: (r1_tarski(A_49, A_4) | ~m1_subset_1(A_49, k1_zfmisc_1(A_4)))), inference(negUnitSimplification, [status(thm)], [c_16, c_61])).
% 3.06/1.46  tff(c_215, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_211, c_64])).
% 3.06/1.46  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.46  tff(c_229, plain, (![A_88]: (r1_tarski(A_88, '#skF_5') | ~r1_tarski(A_88, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_215, c_2])).
% 3.06/1.46  tff(c_237, plain, (![A_20]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_6', A_20)), '#skF_5') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_105, c_229])).
% 3.06/1.46  tff(c_249, plain, (![A_20]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_6', A_20)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_237])).
% 3.06/1.46  tff(c_520, plain, (![C_127, A_128, B_129]: (m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~r1_tarski(k2_relat_1(C_127), B_129) | ~r1_tarski(k1_relat_1(C_127), A_128) | ~v1_relat_1(C_127))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.06/1.46  tff(c_373, plain, (![A_107, B_108, C_109, D_110]: (k5_relset_1(A_107, B_108, C_109, D_110)=k7_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.06/1.46  tff(c_380, plain, (![D_110]: (k5_relset_1('#skF_3', '#skF_5', '#skF_6', D_110)=k7_relat_1('#skF_6', D_110))), inference(resolution, [status(thm)], [c_42, c_373])).
% 3.06/1.46  tff(c_40, plain, (~m1_subset_1(k5_relset_1('#skF_3', '#skF_5', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.06/1.46  tff(c_381, plain, (~m1_subset_1(k7_relat_1('#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_40])).
% 3.06/1.46  tff(c_523, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_4')), '#skF_5') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_4')), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_520, c_381])).
% 3.06/1.46  tff(c_539, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_4')), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_523])).
% 3.06/1.46  tff(c_545, plain, (~v1_relat_1(k7_relat_1('#skF_6', '#skF_4'))), inference(splitLeft, [status(thm)], [c_539])).
% 3.06/1.46  tff(c_548, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_83, c_545])).
% 3.06/1.46  tff(c_552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_548])).
% 3.06/1.46  tff(c_553, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_539])).
% 3.06/1.46  tff(c_557, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_553])).
% 3.06/1.46  tff(c_561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_557])).
% 3.06/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.46  
% 3.06/1.46  Inference rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Ref     : 0
% 3.06/1.46  #Sup     : 111
% 3.06/1.46  #Fact    : 0
% 3.06/1.46  #Define  : 0
% 3.06/1.46  #Split   : 2
% 3.06/1.46  #Chain   : 0
% 3.06/1.46  #Close   : 0
% 3.06/1.46  
% 3.06/1.46  Ordering : KBO
% 3.06/1.46  
% 3.06/1.46  Simplification rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Subsume      : 14
% 3.06/1.46  #Demod        : 21
% 3.06/1.46  #Tautology    : 11
% 3.06/1.46  #SimpNegUnit  : 1
% 3.06/1.46  #BackRed      : 1
% 3.06/1.46  
% 3.06/1.46  #Partial instantiations: 0
% 3.06/1.46  #Strategies tried      : 1
% 3.06/1.46  
% 3.06/1.46  Timing (in seconds)
% 3.06/1.46  ----------------------
% 3.06/1.47  Preprocessing        : 0.33
% 3.06/1.47  Parsing              : 0.17
% 3.06/1.47  CNF conversion       : 0.02
% 3.06/1.47  Main loop            : 0.36
% 3.06/1.47  Inferencing          : 0.13
% 3.06/1.47  Reduction            : 0.10
% 3.06/1.47  Demodulation         : 0.06
% 3.06/1.47  BG Simplification    : 0.02
% 3.06/1.47  Subsumption          : 0.08
% 3.06/1.47  Abstraction          : 0.02
% 3.06/1.47  MUC search           : 0.00
% 3.06/1.47  Cooper               : 0.00
% 3.06/1.47  Total                : 0.73
% 3.06/1.47  Index Insertion      : 0.00
% 3.06/1.47  Index Deletion       : 0.00
% 3.06/1.47  Index Matching       : 0.00
% 3.06/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
