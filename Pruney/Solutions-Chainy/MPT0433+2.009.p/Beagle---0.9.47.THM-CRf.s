%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:15 EST 2020

% Result     : Theorem 29.01s
% Output     : CNFRefutation 29.01s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 203 expanded)
%              Number of leaves         :   26 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 311 expanded)
%              Number of equality atoms :   22 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_130,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(B_47,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_16,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_136,plain,(
    ! [B_47,A_46] : k3_xboole_0(B_47,A_46) = k3_xboole_0(A_46,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_65,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_10])).

tff(c_229,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(A_54,B_55)
      | ~ r1_tarski(A_54,k3_xboole_0(B_55,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_241,plain,(
    ! [B_57,C_58] : r1_tarski(k3_xboole_0(B_57,C_58),B_57) ),
    inference(resolution,[status(thm)],[c_71,c_229])).

tff(c_251,plain,(
    ! [B_47,A_46] : r1_tarski(k3_xboole_0(B_47,A_46),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_241])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_192,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_347,plain,(
    ! [A_68,B_69] :
      ( v1_relat_1(A_68)
      | ~ v1_relat_1(B_69)
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_20,c_192])).

tff(c_364,plain,(
    ! [B_47,A_46] :
      ( v1_relat_1(k3_xboole_0(B_47,A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_251,c_347])).

tff(c_326,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,k3_xboole_0(B_66,C_67))
      | ~ r1_tarski(A_65,C_67)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56399,plain,(
    ! [A_716,B_717,C_718] :
      ( k2_xboole_0(A_716,k3_xboole_0(B_717,C_718)) = k3_xboole_0(B_717,C_718)
      | ~ r1_tarski(A_716,C_718)
      | ~ r1_tarski(A_716,B_717) ) ),
    inference(resolution,[status(thm)],[c_326,c_2])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56443,plain,(
    ! [B_717,C_718] :
      ( k3_xboole_0(B_717,C_718) = B_717
      | ~ r1_tarski(B_717,C_718)
      | ~ r1_tarski(B_717,B_717) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56399,c_8])).

tff(c_56521,plain,(
    ! [B_719,C_720] :
      ( k3_xboole_0(B_719,C_720) = B_719
      | ~ r1_tarski(B_719,C_720) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_56443])).

tff(c_56564,plain,(
    ! [A_32] : k3_xboole_0(A_32,A_32) = A_32 ),
    inference(resolution,[status(thm)],[c_71,c_56521])).

tff(c_55859,plain,(
    ! [A_677,B_678] :
      ( k2_xboole_0(k1_relat_1(A_677),k1_relat_1(B_678)) = k1_relat_1(k2_xboole_0(A_677,B_678))
      | ~ v1_relat_1(B_678)
      | ~ v1_relat_1(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_55872,plain,(
    ! [A_677,B_678] :
      ( r1_tarski(k1_relat_1(A_677),k1_relat_1(k2_xboole_0(A_677,B_678)))
      | ~ v1_relat_1(B_678)
      | ~ v1_relat_1(A_677) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55859,c_10])).

tff(c_59801,plain,(
    ! [A_773,B_774,C_775] :
      ( r1_tarski(k1_relat_1(A_773),k1_relat_1(k3_xboole_0(B_774,C_775)))
      | ~ v1_relat_1(k3_xboole_0(B_774,C_775))
      | ~ v1_relat_1(A_773)
      | ~ r1_tarski(A_773,C_775)
      | ~ r1_tarski(A_773,B_774) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56399,c_55872])).

tff(c_69088,plain,(
    ! [A_903,A_904,B_905] :
      ( r1_tarski(k1_relat_1(A_903),k1_relat_1(k3_xboole_0(A_904,B_905)))
      | ~ v1_relat_1(k3_xboole_0(B_905,A_904))
      | ~ v1_relat_1(A_903)
      | ~ r1_tarski(A_903,A_904)
      | ~ r1_tarski(A_903,B_905) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_59801])).

tff(c_69164,plain,(
    ! [A_903,A_32] :
      ( r1_tarski(k1_relat_1(A_903),k1_relat_1(A_32))
      | ~ v1_relat_1(k3_xboole_0(A_32,A_32))
      | ~ v1_relat_1(A_903)
      | ~ r1_tarski(A_903,A_32)
      | ~ r1_tarski(A_903,A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56564,c_69088])).

tff(c_120514,plain,(
    ! [A_1289,A_1290] :
      ( r1_tarski(k1_relat_1(A_1289),k1_relat_1(A_1290))
      | ~ v1_relat_1(A_1290)
      | ~ v1_relat_1(A_1289)
      | ~ r1_tarski(A_1289,A_1290)
      | ~ r1_tarski(A_1289,A_1290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56564,c_69164])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_256,plain,(
    ! [B_57,C_58] : k2_xboole_0(k3_xboole_0(B_57,C_58),B_57) = B_57 ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_77,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_399,plain,(
    ! [A_76,B_77] :
      ( k2_xboole_0(k1_relat_1(A_76),k1_relat_1(B_77)) = k1_relat_1(k2_xboole_0(A_76,B_77))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_706,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(k1_relat_1(A_101),k1_relat_1(k2_xboole_0(A_101,B_102)))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_10])).

tff(c_2821,plain,(
    ! [A_157,B_158] :
      ( r1_tarski(k1_relat_1(A_157),k1_relat_1(k2_xboole_0(A_157,B_158)))
      | ~ v1_relat_1(k2_xboole_0(A_157,B_158))
      | ~ v1_relat_1(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_706])).

tff(c_2863,plain,(
    ! [B_57,C_58] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(B_57,C_58)),k1_relat_1(B_57))
      | ~ v1_relat_1(k2_xboole_0(k3_xboole_0(B_57,C_58),B_57))
      | ~ v1_relat_1(k3_xboole_0(B_57,C_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_2821])).

tff(c_55660,plain,(
    ! [B_669,C_670] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(B_669,C_670)),k1_relat_1(B_669))
      | ~ v1_relat_1(B_669)
      | ~ v1_relat_1(k3_xboole_0(B_669,C_670)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_2863])).

tff(c_26,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_343,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_326,c_26])).

tff(c_368,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_55678,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_55660,c_368])).

tff(c_55790,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_55678])).

tff(c_55819,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_364,c_55790])).

tff(c_55826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_55819])).

tff(c_55827,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_120547,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_120514,c_55827])).

tff(c_120568,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_28,c_120547])).

tff(c_120573,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_364,c_120568])).

tff(c_120580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_120573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:50:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.01/17.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.01/17.75  
% 29.01/17.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.01/17.75  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 29.01/17.75  
% 29.01/17.75  %Foreground sorts:
% 29.01/17.75  
% 29.01/17.75  
% 29.01/17.75  %Background operators:
% 29.01/17.75  
% 29.01/17.75  
% 29.01/17.75  %Foreground operators:
% 29.01/17.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.01/17.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.01/17.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 29.01/17.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 29.01/17.75  tff('#skF_2', type, '#skF_2': $i).
% 29.01/17.75  tff('#skF_1', type, '#skF_1': $i).
% 29.01/17.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.01/17.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.01/17.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.01/17.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.01/17.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.01/17.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.01/17.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.01/17.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.01/17.75  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 29.01/17.75  
% 29.01/17.77  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 29.01/17.77  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 29.01/17.77  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 29.01/17.77  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 29.01/17.77  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 29.01/17.77  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 29.01/17.77  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 29.01/17.77  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 29.01/17.77  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 29.01/17.77  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 29.01/17.77  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 29.01/17.77  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 29.01/17.77  tff(c_12, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.01/17.77  tff(c_110, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.01/17.77  tff(c_130, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(B_47, A_46))), inference(superposition, [status(thm), theory('equality')], [c_12, c_110])).
% 29.01/17.77  tff(c_16, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.01/17.77  tff(c_136, plain, (![B_47, A_46]: (k3_xboole_0(B_47, A_46)=k3_xboole_0(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_130, c_16])).
% 29.01/17.77  tff(c_65, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k3_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.01/17.77  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.01/17.77  tff(c_71, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_65, c_10])).
% 29.01/17.77  tff(c_229, plain, (![A_54, B_55, C_56]: (r1_tarski(A_54, B_55) | ~r1_tarski(A_54, k3_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.01/17.77  tff(c_241, plain, (![B_57, C_58]: (r1_tarski(k3_xboole_0(B_57, C_58), B_57))), inference(resolution, [status(thm)], [c_71, c_229])).
% 29.01/17.77  tff(c_251, plain, (![B_47, A_46]: (r1_tarski(k3_xboole_0(B_47, A_46), A_46))), inference(superposition, [status(thm), theory('equality')], [c_136, c_241])).
% 29.01/17.77  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 29.01/17.77  tff(c_192, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 29.01/17.77  tff(c_347, plain, (![A_68, B_69]: (v1_relat_1(A_68) | ~v1_relat_1(B_69) | ~r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_20, c_192])).
% 29.01/17.77  tff(c_364, plain, (![B_47, A_46]: (v1_relat_1(k3_xboole_0(B_47, A_46)) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_251, c_347])).
% 29.01/17.77  tff(c_326, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, k3_xboole_0(B_66, C_67)) | ~r1_tarski(A_65, C_67) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.01/17.77  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.01/17.77  tff(c_56399, plain, (![A_716, B_717, C_718]: (k2_xboole_0(A_716, k3_xboole_0(B_717, C_718))=k3_xboole_0(B_717, C_718) | ~r1_tarski(A_716, C_718) | ~r1_tarski(A_716, B_717))), inference(resolution, [status(thm)], [c_326, c_2])).
% 29.01/17.77  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.01/17.77  tff(c_56443, plain, (![B_717, C_718]: (k3_xboole_0(B_717, C_718)=B_717 | ~r1_tarski(B_717, C_718) | ~r1_tarski(B_717, B_717))), inference(superposition, [status(thm), theory('equality')], [c_56399, c_8])).
% 29.01/17.77  tff(c_56521, plain, (![B_719, C_720]: (k3_xboole_0(B_719, C_720)=B_719 | ~r1_tarski(B_719, C_720))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_56443])).
% 29.01/17.77  tff(c_56564, plain, (![A_32]: (k3_xboole_0(A_32, A_32)=A_32)), inference(resolution, [status(thm)], [c_71, c_56521])).
% 29.01/17.77  tff(c_55859, plain, (![A_677, B_678]: (k2_xboole_0(k1_relat_1(A_677), k1_relat_1(B_678))=k1_relat_1(k2_xboole_0(A_677, B_678)) | ~v1_relat_1(B_678) | ~v1_relat_1(A_677))), inference(cnfTransformation, [status(thm)], [f_67])).
% 29.01/17.77  tff(c_55872, plain, (![A_677, B_678]: (r1_tarski(k1_relat_1(A_677), k1_relat_1(k2_xboole_0(A_677, B_678))) | ~v1_relat_1(B_678) | ~v1_relat_1(A_677))), inference(superposition, [status(thm), theory('equality')], [c_55859, c_10])).
% 29.01/17.77  tff(c_59801, plain, (![A_773, B_774, C_775]: (r1_tarski(k1_relat_1(A_773), k1_relat_1(k3_xboole_0(B_774, C_775))) | ~v1_relat_1(k3_xboole_0(B_774, C_775)) | ~v1_relat_1(A_773) | ~r1_tarski(A_773, C_775) | ~r1_tarski(A_773, B_774))), inference(superposition, [status(thm), theory('equality')], [c_56399, c_55872])).
% 29.01/17.77  tff(c_69088, plain, (![A_903, A_904, B_905]: (r1_tarski(k1_relat_1(A_903), k1_relat_1(k3_xboole_0(A_904, B_905))) | ~v1_relat_1(k3_xboole_0(B_905, A_904)) | ~v1_relat_1(A_903) | ~r1_tarski(A_903, A_904) | ~r1_tarski(A_903, B_905))), inference(superposition, [status(thm), theory('equality')], [c_136, c_59801])).
% 29.01/17.77  tff(c_69164, plain, (![A_903, A_32]: (r1_tarski(k1_relat_1(A_903), k1_relat_1(A_32)) | ~v1_relat_1(k3_xboole_0(A_32, A_32)) | ~v1_relat_1(A_903) | ~r1_tarski(A_903, A_32) | ~r1_tarski(A_903, A_32))), inference(superposition, [status(thm), theory('equality')], [c_56564, c_69088])).
% 29.01/17.77  tff(c_120514, plain, (![A_1289, A_1290]: (r1_tarski(k1_relat_1(A_1289), k1_relat_1(A_1290)) | ~v1_relat_1(A_1290) | ~v1_relat_1(A_1289) | ~r1_tarski(A_1289, A_1290) | ~r1_tarski(A_1289, A_1290))), inference(demodulation, [status(thm), theory('equality')], [c_56564, c_69164])).
% 29.01/17.77  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 29.01/17.77  tff(c_256, plain, (![B_57, C_58]: (k2_xboole_0(k3_xboole_0(B_57, C_58), B_57)=B_57)), inference(resolution, [status(thm)], [c_241, c_2])).
% 29.01/17.77  tff(c_77, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.01/17.77  tff(c_81, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_10, c_77])).
% 29.01/17.77  tff(c_399, plain, (![A_76, B_77]: (k2_xboole_0(k1_relat_1(A_76), k1_relat_1(B_77))=k1_relat_1(k2_xboole_0(A_76, B_77)) | ~v1_relat_1(B_77) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_67])).
% 29.01/17.77  tff(c_706, plain, (![A_101, B_102]: (r1_tarski(k1_relat_1(A_101), k1_relat_1(k2_xboole_0(A_101, B_102))) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_399, c_10])).
% 29.01/17.77  tff(c_2821, plain, (![A_157, B_158]: (r1_tarski(k1_relat_1(A_157), k1_relat_1(k2_xboole_0(A_157, B_158))) | ~v1_relat_1(k2_xboole_0(A_157, B_158)) | ~v1_relat_1(A_157))), inference(superposition, [status(thm), theory('equality')], [c_81, c_706])).
% 29.01/17.77  tff(c_2863, plain, (![B_57, C_58]: (r1_tarski(k1_relat_1(k3_xboole_0(B_57, C_58)), k1_relat_1(B_57)) | ~v1_relat_1(k2_xboole_0(k3_xboole_0(B_57, C_58), B_57)) | ~v1_relat_1(k3_xboole_0(B_57, C_58)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_2821])).
% 29.01/17.77  tff(c_55660, plain, (![B_669, C_670]: (r1_tarski(k1_relat_1(k3_xboole_0(B_669, C_670)), k1_relat_1(B_669)) | ~v1_relat_1(B_669) | ~v1_relat_1(k3_xboole_0(B_669, C_670)))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_2863])).
% 29.01/17.77  tff(c_26, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 29.01/17.77  tff(c_343, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_326, c_26])).
% 29.01/17.77  tff(c_368, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_343])).
% 29.01/17.77  tff(c_55678, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_55660, c_368])).
% 29.01/17.77  tff(c_55790, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_55678])).
% 29.01/17.77  tff(c_55819, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_364, c_55790])).
% 29.01/17.77  tff(c_55826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_55819])).
% 29.01/17.77  tff(c_55827, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_343])).
% 29.01/17.77  tff(c_120547, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_120514, c_55827])).
% 29.01/17.77  tff(c_120568, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_28, c_120547])).
% 29.01/17.77  tff(c_120573, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_364, c_120568])).
% 29.01/17.77  tff(c_120580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_120573])).
% 29.01/17.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.01/17.77  
% 29.01/17.77  Inference rules
% 29.01/17.77  ----------------------
% 29.01/17.77  #Ref     : 0
% 29.01/17.77  #Sup     : 31728
% 29.01/17.77  #Fact    : 0
% 29.01/17.77  #Define  : 0
% 29.01/17.77  #Split   : 2
% 29.01/17.77  #Chain   : 0
% 29.01/17.77  #Close   : 0
% 29.01/17.77  
% 29.01/17.77  Ordering : KBO
% 29.01/17.77  
% 29.01/17.77  Simplification rules
% 29.01/17.77  ----------------------
% 29.01/17.77  #Subsume      : 6010
% 29.01/17.77  #Demod        : 18072
% 29.01/17.77  #Tautology    : 13327
% 29.01/17.77  #SimpNegUnit  : 8
% 29.01/17.77  #BackRed      : 0
% 29.01/17.77  
% 29.01/17.77  #Partial instantiations: 0
% 29.01/17.77  #Strategies tried      : 1
% 29.01/17.77  
% 29.01/17.77  Timing (in seconds)
% 29.01/17.77  ----------------------
% 29.01/17.77  Preprocessing        : 0.30
% 29.01/17.77  Parsing              : 0.16
% 29.01/17.77  CNF conversion       : 0.02
% 29.01/17.77  Main loop            : 16.71
% 29.01/17.77  Inferencing          : 2.46
% 29.01/17.77  Reduction            : 9.03
% 29.01/17.77  Demodulation         : 8.17
% 29.01/17.77  BG Simplification    : 0.33
% 29.01/17.77  Subsumption          : 4.23
% 29.01/17.77  Abstraction          : 0.56
% 29.01/17.77  MUC search           : 0.00
% 29.01/17.77  Cooper               : 0.00
% 29.01/17.77  Total                : 17.04
% 29.01/17.77  Index Insertion      : 0.00
% 29.01/17.77  Index Deletion       : 0.00
% 29.01/17.77  Index Matching       : 0.00
% 29.01/17.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
