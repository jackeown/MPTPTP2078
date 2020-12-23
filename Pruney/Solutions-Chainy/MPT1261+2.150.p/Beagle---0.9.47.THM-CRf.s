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
% DateTime   : Thu Dec  3 10:21:33 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 158 expanded)
%              Number of leaves         :   39 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 281 expanded)
%              Number of equality atoms :   67 ( 104 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_70,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5617,plain,(
    ! [A_190,B_191,C_192] :
      ( k7_subset_1(A_190,B_191,C_192) = k4_xboole_0(B_191,C_192)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5620,plain,(
    ! [C_192] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_192) = k4_xboole_0('#skF_2',C_192) ),
    inference(resolution,[status(thm)],[c_36,c_5617])).

tff(c_42,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_106,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1749,plain,(
    ! [B_111,A_112] :
      ( v4_pre_topc(B_111,A_112)
      | k2_pre_topc(A_112,B_111) != B_111
      | ~ v2_pre_topc(A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1755,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1749])).

tff(c_1759,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_1755])).

tff(c_1760,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_1759])).

tff(c_2026,plain,(
    ! [A_115,B_116] :
      ( k4_subset_1(u1_struct_0(A_115),B_116,k2_tops_1(A_115,B_116)) = k2_pre_topc(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2030,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2026])).

tff(c_2034,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2030])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_252,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_48])).

tff(c_398,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_subset_1(A_64,B_65,C_66) = k4_xboole_0(B_65,C_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_489,plain,(
    ! [C_70] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_70) = k4_xboole_0('#skF_2',C_70) ),
    inference(resolution,[status(thm)],[c_36,c_398])).

tff(c_501,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_489])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [A_47] : k3_xboole_0(k1_xboole_0,A_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_107])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_47] : k3_xboole_0(A_47,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_2])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_203,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_221,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_203])).

tff(c_224,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_221])).

tff(c_68,plain,(
    ! [A_40,B_41] : r1_tarski(k4_xboole_0(A_40,B_41),A_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_68])).

tff(c_117,plain,(
    ! [A_13] : k3_xboole_0(A_13,A_13) = A_13 ),
    inference(resolution,[status(thm)],[c_71,c_107])).

tff(c_327,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_339,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k4_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_327])).

tff(c_352,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_339])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_504,plain,(
    ! [A_71,B_72] : k3_xboole_0(k4_xboole_0(A_71,B_72),A_71) = k4_xboole_0(A_71,B_72) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_513,plain,(
    ! [A_71,B_72] : k5_xboole_0(k4_xboole_0(A_71,B_72),k4_xboole_0(A_71,B_72)) = k4_xboole_0(k4_xboole_0(A_71,B_72),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_4])).

tff(c_559,plain,(
    ! [A_71,B_72] : k4_xboole_0(k4_xboole_0(A_71,B_72),A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_513])).

tff(c_767,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_559])).

tff(c_14,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_800,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_14])).

tff(c_812,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_800])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_tops_1(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1042,plain,(
    ! [A_91,B_92,C_93] :
      ( k4_subset_1(A_91,B_92,C_93) = k2_xboole_0(B_92,C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_91))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5055,plain,(
    ! [A_158,B_159,B_160] :
      ( k4_subset_1(u1_struct_0(A_158),B_159,k2_tops_1(A_158,B_160)) = k2_xboole_0(B_159,k2_tops_1(A_158,B_160))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_28,c_1042])).

tff(c_5059,plain,(
    ! [B_160] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_160)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_160))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_5055])).

tff(c_5067,plain,(
    ! [B_161] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_161)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_161))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5059])).

tff(c_5074,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_5067])).

tff(c_5079,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2034,c_812,c_5074])).

tff(c_5081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1760,c_5079])).

tff(c_5082,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_5716,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5620,c_5082])).

tff(c_5083,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6485,plain,(
    ! [A_224,B_225] :
      ( r1_tarski(k2_tops_1(A_224,B_225),B_225)
      | ~ v4_pre_topc(B_225,A_224)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6489,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_6485])).

tff(c_6493,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5083,c_6489])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6497,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6493,c_8])).

tff(c_6543,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6497,c_2])).

tff(c_6859,plain,(
    ! [A_231,B_232] :
      ( k7_subset_1(u1_struct_0(A_231),B_232,k2_tops_1(A_231,B_232)) = k1_tops_1(A_231,B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6863,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_6859])).

tff(c_6867,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5620,c_6863])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6889,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6867,c_18])).

tff(c_6898,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6543,c_6889])).

tff(c_6900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5716,c_6898])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.13  
% 5.60/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.13  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.60/2.13  
% 5.60/2.13  %Foreground sorts:
% 5.60/2.13  
% 5.60/2.13  
% 5.60/2.13  %Background operators:
% 5.60/2.13  
% 5.60/2.13  
% 5.60/2.13  %Foreground operators:
% 5.60/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.60/2.13  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.60/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.60/2.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.60/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.60/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.60/2.13  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.60/2.13  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.60/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.60/2.13  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.60/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.60/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.13  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.60/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.60/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.60/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.60/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.60/2.13  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.60/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.13  
% 5.69/2.14  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.69/2.14  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.69/2.14  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.69/2.14  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.69/2.15  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.69/2.15  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.69/2.15  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.69/2.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.69/2.15  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.69/2.15  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.69/2.15  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.69/2.15  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.69/2.15  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.69/2.15  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.69/2.15  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.69/2.15  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.69/2.15  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.69/2.15  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.69/2.15  tff(c_5617, plain, (![A_190, B_191, C_192]: (k7_subset_1(A_190, B_191, C_192)=k4_xboole_0(B_191, C_192) | ~m1_subset_1(B_191, k1_zfmisc_1(A_190)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.69/2.15  tff(c_5620, plain, (![C_192]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_192)=k4_xboole_0('#skF_2', C_192))), inference(resolution, [status(thm)], [c_36, c_5617])).
% 5.69/2.15  tff(c_42, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.69/2.15  tff(c_106, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 5.69/2.15  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.69/2.15  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.69/2.15  tff(c_1749, plain, (![B_111, A_112]: (v4_pre_topc(B_111, A_112) | k2_pre_topc(A_112, B_111)!=B_111 | ~v2_pre_topc(A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.69/2.15  tff(c_1755, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1749])).
% 5.69/2.15  tff(c_1759, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_1755])).
% 5.69/2.15  tff(c_1760, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_106, c_1759])).
% 5.69/2.15  tff(c_2026, plain, (![A_115, B_116]: (k4_subset_1(u1_struct_0(A_115), B_116, k2_tops_1(A_115, B_116))=k2_pre_topc(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.69/2.15  tff(c_2030, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2026])).
% 5.69/2.15  tff(c_2034, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2030])).
% 5.69/2.15  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.69/2.15  tff(c_48, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.69/2.15  tff(c_252, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_106, c_48])).
% 5.69/2.15  tff(c_398, plain, (![A_64, B_65, C_66]: (k7_subset_1(A_64, B_65, C_66)=k4_xboole_0(B_65, C_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.69/2.15  tff(c_489, plain, (![C_70]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_70)=k4_xboole_0('#skF_2', C_70))), inference(resolution, [status(thm)], [c_36, c_398])).
% 5.69/2.15  tff(c_501, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_252, c_489])).
% 5.69/2.15  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.15  tff(c_107, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.69/2.15  tff(c_120, plain, (![A_47]: (k3_xboole_0(k1_xboole_0, A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_107])).
% 5.69/2.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.69/2.15  tff(c_128, plain, (![A_47]: (k3_xboole_0(A_47, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_120, c_2])).
% 5.69/2.15  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.69/2.15  tff(c_203, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.69/2.15  tff(c_221, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_203])).
% 5.69/2.15  tff(c_224, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_128, c_221])).
% 5.69/2.15  tff(c_68, plain, (![A_40, B_41]: (r1_tarski(k4_xboole_0(A_40, B_41), A_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.69/2.15  tff(c_71, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_68])).
% 5.69/2.15  tff(c_117, plain, (![A_13]: (k3_xboole_0(A_13, A_13)=A_13)), inference(resolution, [status(thm)], [c_71, c_107])).
% 5.69/2.15  tff(c_327, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.69/2.15  tff(c_339, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k4_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_117, c_327])).
% 5.69/2.15  tff(c_352, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_339])).
% 5.69/2.15  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.69/2.15  tff(c_504, plain, (![A_71, B_72]: (k3_xboole_0(k4_xboole_0(A_71, B_72), A_71)=k4_xboole_0(A_71, B_72))), inference(resolution, [status(thm)], [c_12, c_107])).
% 5.69/2.15  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.69/2.15  tff(c_513, plain, (![A_71, B_72]: (k5_xboole_0(k4_xboole_0(A_71, B_72), k4_xboole_0(A_71, B_72))=k4_xboole_0(k4_xboole_0(A_71, B_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_504, c_4])).
% 5.69/2.15  tff(c_559, plain, (![A_71, B_72]: (k4_xboole_0(k4_xboole_0(A_71, B_72), A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_352, c_513])).
% 5.69/2.15  tff(c_767, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_501, c_559])).
% 5.69/2.15  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.69/2.15  tff(c_800, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_767, c_14])).
% 5.69/2.15  tff(c_812, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_800])).
% 5.69/2.15  tff(c_28, plain, (![A_25, B_26]: (m1_subset_1(k2_tops_1(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.69/2.15  tff(c_1042, plain, (![A_91, B_92, C_93]: (k4_subset_1(A_91, B_92, C_93)=k2_xboole_0(B_92, C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(A_91)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.69/2.15  tff(c_5055, plain, (![A_158, B_159, B_160]: (k4_subset_1(u1_struct_0(A_158), B_159, k2_tops_1(A_158, B_160))=k2_xboole_0(B_159, k2_tops_1(A_158, B_160)) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(resolution, [status(thm)], [c_28, c_1042])).
% 5.69/2.15  tff(c_5059, plain, (![B_160]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_160))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_160)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_5055])).
% 5.69/2.15  tff(c_5067, plain, (![B_161]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_161))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_161)) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5059])).
% 5.69/2.15  tff(c_5074, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_5067])).
% 5.69/2.15  tff(c_5079, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2034, c_812, c_5074])).
% 5.69/2.15  tff(c_5081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1760, c_5079])).
% 5.69/2.15  tff(c_5082, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 5.69/2.15  tff(c_5716, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5620, c_5082])).
% 5.69/2.15  tff(c_5083, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 5.69/2.15  tff(c_6485, plain, (![A_224, B_225]: (r1_tarski(k2_tops_1(A_224, B_225), B_225) | ~v4_pre_topc(B_225, A_224) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.69/2.15  tff(c_6489, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_6485])).
% 5.69/2.15  tff(c_6493, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5083, c_6489])).
% 5.69/2.15  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.69/2.15  tff(c_6497, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6493, c_8])).
% 5.69/2.15  tff(c_6543, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6497, c_2])).
% 5.69/2.15  tff(c_6859, plain, (![A_231, B_232]: (k7_subset_1(u1_struct_0(A_231), B_232, k2_tops_1(A_231, B_232))=k1_tops_1(A_231, B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.69/2.15  tff(c_6863, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_6859])).
% 5.69/2.15  tff(c_6867, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5620, c_6863])).
% 5.69/2.15  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.69/2.15  tff(c_6889, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6867, c_18])).
% 5.69/2.15  tff(c_6898, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6543, c_6889])).
% 5.69/2.15  tff(c_6900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5716, c_6898])).
% 5.69/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.15  
% 5.69/2.15  Inference rules
% 5.69/2.15  ----------------------
% 5.69/2.15  #Ref     : 0
% 5.69/2.15  #Sup     : 1684
% 5.69/2.15  #Fact    : 0
% 5.69/2.15  #Define  : 0
% 5.69/2.15  #Split   : 2
% 5.69/2.15  #Chain   : 0
% 5.69/2.15  #Close   : 0
% 5.69/2.15  
% 5.69/2.15  Ordering : KBO
% 5.69/2.15  
% 5.69/2.15  Simplification rules
% 5.69/2.15  ----------------------
% 5.69/2.15  #Subsume      : 73
% 5.69/2.15  #Demod        : 2376
% 5.69/2.15  #Tautology    : 1417
% 5.69/2.15  #SimpNegUnit  : 4
% 5.69/2.15  #BackRed      : 3
% 5.69/2.15  
% 5.69/2.15  #Partial instantiations: 0
% 5.69/2.15  #Strategies tried      : 1
% 5.69/2.15  
% 5.69/2.15  Timing (in seconds)
% 5.69/2.15  ----------------------
% 5.69/2.15  Preprocessing        : 0.33
% 5.69/2.15  Parsing              : 0.18
% 5.69/2.15  CNF conversion       : 0.02
% 5.69/2.15  Main loop            : 1.05
% 5.69/2.15  Inferencing          : 0.31
% 5.69/2.15  Reduction            : 0.52
% 5.69/2.15  Demodulation         : 0.44
% 5.69/2.15  BG Simplification    : 0.03
% 5.69/2.15  Subsumption          : 0.12
% 5.69/2.15  Abstraction          : 0.05
% 5.69/2.15  MUC search           : 0.00
% 5.69/2.15  Cooper               : 0.00
% 5.69/2.15  Total                : 1.42
% 5.69/2.15  Index Insertion      : 0.00
% 5.69/2.15  Index Deletion       : 0.00
% 5.69/2.15  Index Matching       : 0.00
% 5.69/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
