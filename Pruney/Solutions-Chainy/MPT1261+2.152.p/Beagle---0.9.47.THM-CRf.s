%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:33 EST 2020

% Result     : Theorem 11.37s
% Output     : CNFRefutation 11.45s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 373 expanded)
%              Number of leaves         :   52 ( 147 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 ( 725 expanded)
%              Number of equality atoms :   83 ( 205 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_68,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_26520,plain,(
    ! [A_657,B_658] :
      ( r1_tarski(k1_tops_1(A_657,B_658),B_658)
      | ~ m1_subset_1(B_658,k1_zfmisc_1(u1_struct_0(A_657)))
      | ~ l1_pre_topc(A_657) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_26531,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_26520])).

tff(c_26540,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_26531])).

tff(c_52,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(A_61,k1_zfmisc_1(B_62))
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_25746,plain,(
    ! [A_617,B_618] :
      ( k4_xboole_0(A_617,B_618) = k3_subset_1(A_617,B_618)
      | ~ m1_subset_1(B_618,k1_zfmisc_1(A_617)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_25760,plain,(
    ! [B_62,A_61] :
      ( k4_xboole_0(B_62,A_61) = k3_subset_1(B_62,A_61)
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_52,c_25746])).

tff(c_26556,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26540,c_25760])).

tff(c_26288,plain,(
    ! [A_640,B_641,C_642] :
      ( k7_subset_1(A_640,B_641,C_642) = k4_xboole_0(B_641,C_642)
      | ~ m1_subset_1(B_641,k1_zfmisc_1(A_640)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26303,plain,(
    ! [C_642] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_642) = k4_xboole_0('#skF_2',C_642) ),
    inference(resolution,[status(thm)],[c_68,c_26288])).

tff(c_74,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_212,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2544,plain,(
    ! [B_212,A_213] :
      ( v4_pre_topc(B_212,A_213)
      | k2_pre_topc(A_213,B_212) != B_212
      | ~ v2_pre_topc(A_213)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2562,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_2544])).

tff(c_2573,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_2562])).

tff(c_2574,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_2573])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_32,plain,(
    ! [A_41] : k2_subset_1(A_41) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_44] : m1_subset_1(k2_subset_1(A_44),k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_81,plain,(
    ! [A_44] : m1_subset_1(A_44,k1_zfmisc_1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_377,plain,(
    ! [A_119,B_120] :
      ( k4_xboole_0(A_119,B_120) = k3_subset_1(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_389,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = k3_subset_1(A_44,A_44) ),
    inference(resolution,[status(thm)],[c_81,c_377])).

tff(c_394,plain,(
    ! [A_44] : k3_subset_1(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_389])).

tff(c_547,plain,(
    ! [A_127,B_128] :
      ( k3_subset_1(A_127,k3_subset_1(A_127,B_128)) = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_557,plain,(
    ! [A_44] : k3_subset_1(A_44,k3_subset_1(A_44,A_44)) = A_44 ),
    inference(resolution,[status(thm)],[c_81,c_547])).

tff(c_563,plain,(
    ! [A_44] : k3_subset_1(A_44,k1_xboole_0) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_557])).

tff(c_1048,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k1_tops_1(A_152,B_153),B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1059,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1048])).

tff(c_1068,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1059])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1086,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1068,c_10])).

tff(c_737,plain,(
    ! [A_133,B_134,C_135] :
      ( k7_subset_1(A_133,B_134,C_135) = k4_xboole_0(B_134,C_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_780,plain,(
    ! [C_140] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_140) = k4_xboole_0('#skF_2',C_140) ),
    inference(resolution,[status(thm)],[c_68,c_737])).

tff(c_80,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_114,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_786,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_114])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2394,plain,(
    ! [A_207,B_208,C_209] :
      ( k4_subset_1(A_207,B_208,C_209) = k2_xboole_0(B_208,C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(A_207))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(A_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5983,plain,(
    ! [B_310,B_311,A_312] :
      ( k4_subset_1(B_310,B_311,A_312) = k2_xboole_0(B_311,A_312)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(B_310))
      | ~ r1_tarski(A_312,B_310) ) ),
    inference(resolution,[status(thm)],[c_52,c_2394])).

tff(c_6002,plain,(
    ! [A_313,A_314] :
      ( k4_subset_1(A_313,A_313,A_314) = k2_xboole_0(A_313,A_314)
      | ~ r1_tarski(A_314,A_313) ) ),
    inference(resolution,[status(thm)],[c_81,c_5983])).

tff(c_6051,plain,(
    ! [A_7,B_8] : k4_subset_1(A_7,A_7,k4_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_14,c_6002])).

tff(c_2576,plain,(
    ! [A_214,B_215] :
      ( k4_subset_1(A_214,B_215,A_214) = k2_xboole_0(B_215,A_214)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(A_214)) ) ),
    inference(resolution,[status(thm)],[c_81,c_2394])).

tff(c_2627,plain,(
    ! [B_218,A_219] :
      ( k4_subset_1(B_218,A_219,B_218) = k2_xboole_0(A_219,B_218)
      | ~ r1_tarski(A_219,B_218) ) ),
    inference(resolution,[status(thm)],[c_52,c_2576])).

tff(c_2667,plain,(
    ! [A_7,B_8] : k4_subset_1(A_7,k4_xboole_0(A_7,B_8),A_7) = k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) ),
    inference(resolution,[status(thm)],[c_14,c_2627])).

tff(c_2883,plain,(
    ! [A_228,C_229,B_230] :
      ( k4_subset_1(A_228,C_229,B_230) = k4_subset_1(A_228,B_230,C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(A_228))
      | ~ m1_subset_1(B_230,k1_zfmisc_1(A_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4424,plain,(
    ! [A_272,B_273] :
      ( k4_subset_1(A_272,B_273,A_272) = k4_subset_1(A_272,A_272,B_273)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(A_272)) ) ),
    inference(resolution,[status(thm)],[c_81,c_2883])).

tff(c_4486,plain,(
    ! [B_278,A_279] :
      ( k4_subset_1(B_278,B_278,A_279) = k4_subset_1(B_278,A_279,B_278)
      | ~ r1_tarski(A_279,B_278) ) ),
    inference(resolution,[status(thm)],[c_52,c_4424])).

tff(c_4514,plain,(
    ! [A_7,B_8] : k4_subset_1(A_7,k4_xboole_0(A_7,B_8),A_7) = k4_subset_1(A_7,A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_14,c_4486])).

tff(c_4535,plain,(
    ! [A_7,B_8] : k4_subset_1(A_7,A_7,k4_xboole_0(A_7,B_8)) = k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2667,c_4514])).

tff(c_6206,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6051,c_4535])).

tff(c_6752,plain,(
    ! [A_326,B_327] : k4_subset_1(A_326,k4_xboole_0(A_326,B_327),A_326) = k2_xboole_0(A_326,k4_xboole_0(A_326,B_327)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6206,c_2667])).

tff(c_6836,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_6752])).

tff(c_6889,plain,(
    k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_6836])).

tff(c_391,plain,(
    ! [B_62,A_61] :
      ( k4_xboole_0(B_62,A_61) = k3_subset_1(B_62,A_61)
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_52,c_377])).

tff(c_1072,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1068,c_391])).

tff(c_1082,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_1072])).

tff(c_1281,plain,(
    ! [B_166,A_167,C_168] :
      ( k7_subset_1(B_166,A_167,C_168) = k4_xboole_0(A_167,C_168)
      | ~ r1_tarski(A_167,B_166) ) ),
    inference(resolution,[status(thm)],[c_52,c_737])).

tff(c_1306,plain,(
    ! [C_168] : k7_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'),C_168) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_168) ),
    inference(resolution,[status(thm)],[c_1068,c_1281])).

tff(c_38,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k3_subset_1(A_45,B_46),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1175,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1082,c_38])).

tff(c_7550,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1175])).

tff(c_7553,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_7550])).

tff(c_7557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1068,c_7553])).

tff(c_7559,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1175])).

tff(c_4467,plain,(
    ! [A_275,B_276,C_277] :
      ( k4_subset_1(A_275,k3_subset_1(A_275,B_276),C_277) = k3_subset_1(A_275,k7_subset_1(A_275,B_276,C_277))
      | ~ m1_subset_1(C_277,k1_zfmisc_1(A_275))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(A_275)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14421,plain,(
    ! [A_418,B_419] :
      ( k4_subset_1(A_418,k3_subset_1(A_418,B_419),A_418) = k3_subset_1(A_418,k7_subset_1(A_418,B_419,A_418))
      | ~ m1_subset_1(B_419,k1_zfmisc_1(A_418)) ) ),
    inference(resolution,[status(thm)],[c_81,c_4467])).

tff(c_14425,plain,(
    k4_subset_1('#skF_2',k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),'#skF_2') = k3_subset_1('#skF_2',k7_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_7559,c_14421])).

tff(c_14441,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_1086,c_6889,c_1082,c_1306,c_14425])).

tff(c_3133,plain,(
    ! [A_239,B_240] :
      ( k4_subset_1(u1_struct_0(A_239),B_240,k2_tops_1(A_239,B_240)) = k2_pre_topc(A_239,B_240)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3146,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_3133])).

tff(c_3156,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3146])).

tff(c_58,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k2_tops_1(A_66,B_67),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24619,plain,(
    ! [A_546,B_547,B_548] :
      ( k4_subset_1(u1_struct_0(A_546),B_547,k2_tops_1(A_546,B_548)) = k2_xboole_0(B_547,k2_tops_1(A_546,B_548))
      | ~ m1_subset_1(B_547,k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ m1_subset_1(B_548,k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ l1_pre_topc(A_546) ) ),
    inference(resolution,[status(thm)],[c_58,c_2394])).

tff(c_24632,plain,(
    ! [B_548] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_548)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_548))
      | ~ m1_subset_1(B_548,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_24619])).

tff(c_24852,plain,(
    ! [B_550] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_550)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_550))
      | ~ m1_subset_1(B_550,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24632])).

tff(c_24871,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_24852])).

tff(c_24883,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14441,c_3156,c_24871])).

tff(c_24885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2574,c_24883])).

tff(c_24886,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_25408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24886,c_114])).

tff(c_25409,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_25436,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25409,c_74])).

tff(c_26331,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26303,c_25436])).

tff(c_26724,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26556,c_26331])).

tff(c_26905,plain,(
    ! [A_670,B_671] :
      ( k2_pre_topc(A_670,B_671) = B_671
      | ~ v4_pre_topc(B_671,A_670)
      | ~ m1_subset_1(B_671,k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ l1_pre_topc(A_670) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26920,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_26905])).

tff(c_26930,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_25409,c_26920])).

tff(c_30248,plain,(
    ! [A_777,B_778] :
      ( k7_subset_1(u1_struct_0(A_777),k2_pre_topc(A_777,B_778),k1_tops_1(A_777,B_778)) = k2_tops_1(A_777,B_778)
      | ~ m1_subset_1(B_778,k1_zfmisc_1(u1_struct_0(A_777)))
      | ~ l1_pre_topc(A_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30263,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26930,c_30248])).

tff(c_30270,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_26556,c_26303,c_30263])).

tff(c_30272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26724,c_30270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.37/4.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.45/4.68  
% 11.45/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.45/4.68  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.45/4.68  
% 11.45/4.68  %Foreground sorts:
% 11.45/4.68  
% 11.45/4.68  
% 11.45/4.68  %Background operators:
% 11.45/4.68  
% 11.45/4.68  
% 11.45/4.68  %Foreground operators:
% 11.45/4.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.45/4.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.45/4.68  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.45/4.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.45/4.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.45/4.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.45/4.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.45/4.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.45/4.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.45/4.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.45/4.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.45/4.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.45/4.68  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.45/4.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.45/4.68  tff('#skF_2', type, '#skF_2': $i).
% 11.45/4.68  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.45/4.68  tff('#skF_1', type, '#skF_1': $i).
% 11.45/4.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.45/4.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.45/4.68  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.45/4.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.45/4.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.45/4.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.45/4.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.45/4.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.45/4.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.45/4.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.45/4.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.45/4.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.45/4.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.45/4.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.45/4.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.45/4.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.45/4.68  
% 11.45/4.70  tff(f_160, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 11.45/4.70  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 11.45/4.70  tff(f_98, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.45/4.70  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.45/4.70  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.45/4.70  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 11.45/4.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.45/4.70  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.45/4.70  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 11.45/4.70  tff(f_67, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.45/4.70  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.45/4.70  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.45/4.70  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.45/4.70  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 11.45/4.70  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.45/4.70  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 11.45/4.70  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 11.45/4.70  tff(f_119, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 11.45/4.70  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 11.45/4.70  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.45/4.70  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.45/4.70  tff(c_26520, plain, (![A_657, B_658]: (r1_tarski(k1_tops_1(A_657, B_658), B_658) | ~m1_subset_1(B_658, k1_zfmisc_1(u1_struct_0(A_657))) | ~l1_pre_topc(A_657))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.45/4.70  tff(c_26531, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_26520])).
% 11.45/4.70  tff(c_26540, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_26531])).
% 11.45/4.70  tff(c_52, plain, (![A_61, B_62]: (m1_subset_1(A_61, k1_zfmisc_1(B_62)) | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.45/4.70  tff(c_25746, plain, (![A_617, B_618]: (k4_xboole_0(A_617, B_618)=k3_subset_1(A_617, B_618) | ~m1_subset_1(B_618, k1_zfmisc_1(A_617)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.45/4.70  tff(c_25760, plain, (![B_62, A_61]: (k4_xboole_0(B_62, A_61)=k3_subset_1(B_62, A_61) | ~r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_52, c_25746])).
% 11.45/4.70  tff(c_26556, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26540, c_25760])).
% 11.45/4.70  tff(c_26288, plain, (![A_640, B_641, C_642]: (k7_subset_1(A_640, B_641, C_642)=k4_xboole_0(B_641, C_642) | ~m1_subset_1(B_641, k1_zfmisc_1(A_640)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.45/4.70  tff(c_26303, plain, (![C_642]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_642)=k4_xboole_0('#skF_2', C_642))), inference(resolution, [status(thm)], [c_68, c_26288])).
% 11.45/4.70  tff(c_74, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.45/4.70  tff(c_212, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_74])).
% 11.45/4.70  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.45/4.70  tff(c_2544, plain, (![B_212, A_213]: (v4_pre_topc(B_212, A_213) | k2_pre_topc(A_213, B_212)!=B_212 | ~v2_pre_topc(A_213) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.45/4.70  tff(c_2562, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_2544])).
% 11.45/4.70  tff(c_2573, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_2562])).
% 11.45/4.70  tff(c_2574, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_212, c_2573])).
% 11.45/4.70  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.45/4.70  tff(c_95, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k1_xboole_0 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.45/4.70  tff(c_103, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_95])).
% 11.45/4.70  tff(c_32, plain, (![A_41]: (k2_subset_1(A_41)=A_41)), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.45/4.70  tff(c_36, plain, (![A_44]: (m1_subset_1(k2_subset_1(A_44), k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.45/4.70  tff(c_81, plain, (![A_44]: (m1_subset_1(A_44, k1_zfmisc_1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 11.45/4.70  tff(c_377, plain, (![A_119, B_120]: (k4_xboole_0(A_119, B_120)=k3_subset_1(A_119, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.45/4.70  tff(c_389, plain, (![A_44]: (k4_xboole_0(A_44, A_44)=k3_subset_1(A_44, A_44))), inference(resolution, [status(thm)], [c_81, c_377])).
% 11.45/4.70  tff(c_394, plain, (![A_44]: (k3_subset_1(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_389])).
% 11.45/4.70  tff(c_547, plain, (![A_127, B_128]: (k3_subset_1(A_127, k3_subset_1(A_127, B_128))=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.45/4.70  tff(c_557, plain, (![A_44]: (k3_subset_1(A_44, k3_subset_1(A_44, A_44))=A_44)), inference(resolution, [status(thm)], [c_81, c_547])).
% 11.45/4.70  tff(c_563, plain, (![A_44]: (k3_subset_1(A_44, k1_xboole_0)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_394, c_557])).
% 11.45/4.70  tff(c_1048, plain, (![A_152, B_153]: (r1_tarski(k1_tops_1(A_152, B_153), B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.45/4.70  tff(c_1059, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_1048])).
% 11.45/4.70  tff(c_1068, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1059])).
% 11.45/4.70  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.45/4.70  tff(c_1086, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1068, c_10])).
% 11.45/4.70  tff(c_737, plain, (![A_133, B_134, C_135]: (k7_subset_1(A_133, B_134, C_135)=k4_xboole_0(B_134, C_135) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.45/4.70  tff(c_780, plain, (![C_140]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_140)=k4_xboole_0('#skF_2', C_140))), inference(resolution, [status(thm)], [c_68, c_737])).
% 11.45/4.70  tff(c_80, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 11.45/4.70  tff(c_114, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_80])).
% 11.45/4.70  tff(c_786, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_780, c_114])).
% 11.45/4.70  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.45/4.70  tff(c_2394, plain, (![A_207, B_208, C_209]: (k4_subset_1(A_207, B_208, C_209)=k2_xboole_0(B_208, C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(A_207)) | ~m1_subset_1(B_208, k1_zfmisc_1(A_207)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.45/4.70  tff(c_5983, plain, (![B_310, B_311, A_312]: (k4_subset_1(B_310, B_311, A_312)=k2_xboole_0(B_311, A_312) | ~m1_subset_1(B_311, k1_zfmisc_1(B_310)) | ~r1_tarski(A_312, B_310))), inference(resolution, [status(thm)], [c_52, c_2394])).
% 11.45/4.70  tff(c_6002, plain, (![A_313, A_314]: (k4_subset_1(A_313, A_313, A_314)=k2_xboole_0(A_313, A_314) | ~r1_tarski(A_314, A_313))), inference(resolution, [status(thm)], [c_81, c_5983])).
% 11.45/4.70  tff(c_6051, plain, (![A_7, B_8]: (k4_subset_1(A_7, A_7, k4_xboole_0(A_7, B_8))=k2_xboole_0(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_14, c_6002])).
% 11.45/4.70  tff(c_2576, plain, (![A_214, B_215]: (k4_subset_1(A_214, B_215, A_214)=k2_xboole_0(B_215, A_214) | ~m1_subset_1(B_215, k1_zfmisc_1(A_214)))), inference(resolution, [status(thm)], [c_81, c_2394])).
% 11.45/4.70  tff(c_2627, plain, (![B_218, A_219]: (k4_subset_1(B_218, A_219, B_218)=k2_xboole_0(A_219, B_218) | ~r1_tarski(A_219, B_218))), inference(resolution, [status(thm)], [c_52, c_2576])).
% 11.45/4.70  tff(c_2667, plain, (![A_7, B_8]: (k4_subset_1(A_7, k4_xboole_0(A_7, B_8), A_7)=k2_xboole_0(k4_xboole_0(A_7, B_8), A_7))), inference(resolution, [status(thm)], [c_14, c_2627])).
% 11.45/4.70  tff(c_2883, plain, (![A_228, C_229, B_230]: (k4_subset_1(A_228, C_229, B_230)=k4_subset_1(A_228, B_230, C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(A_228)) | ~m1_subset_1(B_230, k1_zfmisc_1(A_228)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.45/4.70  tff(c_4424, plain, (![A_272, B_273]: (k4_subset_1(A_272, B_273, A_272)=k4_subset_1(A_272, A_272, B_273) | ~m1_subset_1(B_273, k1_zfmisc_1(A_272)))), inference(resolution, [status(thm)], [c_81, c_2883])).
% 11.45/4.70  tff(c_4486, plain, (![B_278, A_279]: (k4_subset_1(B_278, B_278, A_279)=k4_subset_1(B_278, A_279, B_278) | ~r1_tarski(A_279, B_278))), inference(resolution, [status(thm)], [c_52, c_4424])).
% 11.45/4.70  tff(c_4514, plain, (![A_7, B_8]: (k4_subset_1(A_7, k4_xboole_0(A_7, B_8), A_7)=k4_subset_1(A_7, A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_14, c_4486])).
% 11.45/4.70  tff(c_4535, plain, (![A_7, B_8]: (k4_subset_1(A_7, A_7, k4_xboole_0(A_7, B_8))=k2_xboole_0(k4_xboole_0(A_7, B_8), A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2667, c_4514])).
% 11.45/4.70  tff(c_6206, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k2_xboole_0(A_7, k4_xboole_0(A_7, B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_6051, c_4535])).
% 11.45/4.70  tff(c_6752, plain, (![A_326, B_327]: (k4_subset_1(A_326, k4_xboole_0(A_326, B_327), A_326)=k2_xboole_0(A_326, k4_xboole_0(A_326, B_327)))), inference(demodulation, [status(thm), theory('equality')], [c_6206, c_2667])).
% 11.45/4.70  tff(c_6836, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_786, c_6752])).
% 11.45/4.70  tff(c_6889, plain, (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_6836])).
% 11.45/4.70  tff(c_391, plain, (![B_62, A_61]: (k4_xboole_0(B_62, A_61)=k3_subset_1(B_62, A_61) | ~r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_52, c_377])).
% 11.45/4.70  tff(c_1072, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1068, c_391])).
% 11.45/4.70  tff(c_1082, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_786, c_1072])).
% 11.45/4.70  tff(c_1281, plain, (![B_166, A_167, C_168]: (k7_subset_1(B_166, A_167, C_168)=k4_xboole_0(A_167, C_168) | ~r1_tarski(A_167, B_166))), inference(resolution, [status(thm)], [c_52, c_737])).
% 11.45/4.70  tff(c_1306, plain, (![C_168]: (k7_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'), C_168)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_168))), inference(resolution, [status(thm)], [c_1068, c_1281])).
% 11.45/4.70  tff(c_38, plain, (![A_45, B_46]: (m1_subset_1(k3_subset_1(A_45, B_46), k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.45/4.70  tff(c_1175, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1082, c_38])).
% 11.45/4.70  tff(c_7550, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1175])).
% 11.45/4.70  tff(c_7553, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_52, c_7550])).
% 11.45/4.70  tff(c_7557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1068, c_7553])).
% 11.45/4.70  tff(c_7559, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1175])).
% 11.45/4.70  tff(c_4467, plain, (![A_275, B_276, C_277]: (k4_subset_1(A_275, k3_subset_1(A_275, B_276), C_277)=k3_subset_1(A_275, k7_subset_1(A_275, B_276, C_277)) | ~m1_subset_1(C_277, k1_zfmisc_1(A_275)) | ~m1_subset_1(B_276, k1_zfmisc_1(A_275)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.45/4.70  tff(c_14421, plain, (![A_418, B_419]: (k4_subset_1(A_418, k3_subset_1(A_418, B_419), A_418)=k3_subset_1(A_418, k7_subset_1(A_418, B_419, A_418)) | ~m1_subset_1(B_419, k1_zfmisc_1(A_418)))), inference(resolution, [status(thm)], [c_81, c_4467])).
% 11.45/4.70  tff(c_14425, plain, (k4_subset_1('#skF_2', k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')), '#skF_2')=k3_subset_1('#skF_2', k7_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'), '#skF_2'))), inference(resolution, [status(thm)], [c_7559, c_14421])).
% 11.45/4.70  tff(c_14441, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_563, c_1086, c_6889, c_1082, c_1306, c_14425])).
% 11.45/4.70  tff(c_3133, plain, (![A_239, B_240]: (k4_subset_1(u1_struct_0(A_239), B_240, k2_tops_1(A_239, B_240))=k2_pre_topc(A_239, B_240) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.45/4.70  tff(c_3146, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_3133])).
% 11.45/4.70  tff(c_3156, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3146])).
% 11.45/4.70  tff(c_58, plain, (![A_66, B_67]: (m1_subset_1(k2_tops_1(A_66, B_67), k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.45/4.70  tff(c_24619, plain, (![A_546, B_547, B_548]: (k4_subset_1(u1_struct_0(A_546), B_547, k2_tops_1(A_546, B_548))=k2_xboole_0(B_547, k2_tops_1(A_546, B_548)) | ~m1_subset_1(B_547, k1_zfmisc_1(u1_struct_0(A_546))) | ~m1_subset_1(B_548, k1_zfmisc_1(u1_struct_0(A_546))) | ~l1_pre_topc(A_546))), inference(resolution, [status(thm)], [c_58, c_2394])).
% 11.45/4.70  tff(c_24632, plain, (![B_548]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_548))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_548)) | ~m1_subset_1(B_548, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_24619])).
% 11.45/4.70  tff(c_24852, plain, (![B_550]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_550))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_550)) | ~m1_subset_1(B_550, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_24632])).
% 11.45/4.70  tff(c_24871, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_24852])).
% 11.45/4.70  tff(c_24883, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14441, c_3156, c_24871])).
% 11.45/4.70  tff(c_24885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2574, c_24883])).
% 11.45/4.70  tff(c_24886, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_74])).
% 11.45/4.70  tff(c_25408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24886, c_114])).
% 11.45/4.70  tff(c_25409, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_80])).
% 11.45/4.70  tff(c_25436, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25409, c_74])).
% 11.45/4.70  tff(c_26331, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26303, c_25436])).
% 11.45/4.70  tff(c_26724, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26556, c_26331])).
% 11.45/4.70  tff(c_26905, plain, (![A_670, B_671]: (k2_pre_topc(A_670, B_671)=B_671 | ~v4_pre_topc(B_671, A_670) | ~m1_subset_1(B_671, k1_zfmisc_1(u1_struct_0(A_670))) | ~l1_pre_topc(A_670))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.45/4.70  tff(c_26920, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_26905])).
% 11.45/4.70  tff(c_26930, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_25409, c_26920])).
% 11.45/4.70  tff(c_30248, plain, (![A_777, B_778]: (k7_subset_1(u1_struct_0(A_777), k2_pre_topc(A_777, B_778), k1_tops_1(A_777, B_778))=k2_tops_1(A_777, B_778) | ~m1_subset_1(B_778, k1_zfmisc_1(u1_struct_0(A_777))) | ~l1_pre_topc(A_777))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.45/4.70  tff(c_30263, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26930, c_30248])).
% 11.45/4.70  tff(c_30270, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_26556, c_26303, c_30263])).
% 11.45/4.70  tff(c_30272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26724, c_30270])).
% 11.45/4.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.45/4.70  
% 11.45/4.70  Inference rules
% 11.45/4.70  ----------------------
% 11.45/4.70  #Ref     : 4
% 11.45/4.70  #Sup     : 7031
% 11.45/4.70  #Fact    : 0
% 11.45/4.70  #Define  : 0
% 11.45/4.70  #Split   : 13
% 11.45/4.70  #Chain   : 0
% 11.45/4.70  #Close   : 0
% 11.45/4.70  
% 11.45/4.70  Ordering : KBO
% 11.45/4.70  
% 11.45/4.70  Simplification rules
% 11.45/4.70  ----------------------
% 11.45/4.70  #Subsume      : 1267
% 11.45/4.70  #Demod        : 6902
% 11.45/4.70  #Tautology    : 4018
% 11.45/4.70  #SimpNegUnit  : 73
% 11.45/4.70  #BackRed      : 72
% 11.45/4.70  
% 11.45/4.70  #Partial instantiations: 0
% 11.45/4.70  #Strategies tried      : 1
% 11.45/4.70  
% 11.45/4.70  Timing (in seconds)
% 11.45/4.70  ----------------------
% 11.45/4.71  Preprocessing        : 0.36
% 11.45/4.71  Parsing              : 0.19
% 11.45/4.71  CNF conversion       : 0.02
% 11.45/4.71  Main loop            : 3.55
% 11.45/4.71  Inferencing          : 0.81
% 11.45/4.71  Reduction            : 1.71
% 11.45/4.71  Demodulation         : 1.38
% 11.45/4.71  BG Simplification    : 0.09
% 11.45/4.71  Subsumption          : 0.76
% 11.45/4.71  Abstraction          : 0.15
% 11.45/4.71  MUC search           : 0.00
% 11.45/4.71  Cooper               : 0.00
% 11.45/4.71  Total                : 3.96
% 11.45/4.71  Index Insertion      : 0.00
% 11.45/4.71  Index Deletion       : 0.00
% 11.45/4.71  Index Matching       : 0.00
% 11.45/4.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
