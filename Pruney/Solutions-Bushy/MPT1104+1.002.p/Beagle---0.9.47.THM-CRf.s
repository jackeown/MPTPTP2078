%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1104+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:24 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 100 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 190 expanded)
%              Number of equality atoms :   27 (  75 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > m1_subset_1 > l1_struct_0 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( k2_struct_0(A) = k4_subset_1(u1_struct_0(A),B,C)
                    & r1_xboole_0(B,C) )
                 => C = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_30,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_72,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_76,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_24,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_88,plain,(
    k4_subset_1(k2_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_24])).

tff(c_203,plain,(
    ! [A_45,B_46,C_47] :
      ( m1_subset_1(k4_subset_1(A_45,B_46,C_47),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_208,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_203])).

tff(c_211,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_208])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( k7_subset_1(A_10,B_11,C_12) = k4_xboole_0(B_11,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_214,plain,(
    ! [C_12] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_12) = k4_xboole_0(k2_struct_0('#skF_1'),C_12) ),
    inference(resolution,[status(thm)],[c_211,c_10])).

tff(c_20,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_83,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_20])).

tff(c_215,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_83])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_93,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_67,c_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_225,plain,(
    ! [A_49,B_50,C_51] :
      ( k4_subset_1(A_49,B_50,C_51) = k2_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_449,plain,(
    ! [B_68] :
      ( k4_subset_1(k2_struct_0('#skF_1'),B_68,'#skF_3') = k2_xboole_0(B_68,'#skF_3')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_77,c_225])).

tff(c_459,plain,(
    k4_subset_1(k2_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_449])).

tff(c_468,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2,c_459])).

tff(c_14,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_488,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_14])).

tff(c_496,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_488])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_496])).

%------------------------------------------------------------------------------
