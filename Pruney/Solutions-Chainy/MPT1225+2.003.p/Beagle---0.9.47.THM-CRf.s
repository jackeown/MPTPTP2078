%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:27 EST 2020

% Result     : Theorem 13.21s
% Output     : CNFRefutation 13.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 363 expanded)
%              Number of leaves         :   24 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 914 expanded)
%              Number of equality atoms :   42 ( 242 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_31,plain,(
    ! [A_34,B_35,C_36] :
      ( k9_subset_1(A_34,B_35,C_36) = k3_xboole_0(B_35,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [B_35] : k9_subset_1(u1_struct_0('#skF_1'),B_35,'#skF_2') = k3_xboole_0(B_35,'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_107,plain,(
    ! [A_43,C_44,B_45] :
      ( k9_subset_1(A_43,C_44,B_45) = k9_subset_1(A_43,B_45,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_117,plain,(
    ! [B_45] : k9_subset_1(u1_struct_0('#skF_1'),B_45,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_45) ),
    inference(resolution,[status(thm)],[c_26,c_107])).

tff(c_137,plain,(
    ! [B_46] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_46) = k3_xboole_0(B_46,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_117])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_39,plain,(
    ! [B_35] : k9_subset_1(u1_struct_0('#skF_1'),B_35,'#skF_3') = k3_xboole_0(B_35,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_31])).

tff(c_148,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_39])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_228,plain,(
    ! [A_50,B_51] :
      ( k2_pre_topc(A_50,B_51) = B_51
      | ~ v4_pre_topc(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_244,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_257,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_244])).

tff(c_20,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_241,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_228])).

tff(c_254,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20,c_241])).

tff(c_18,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_18])).

tff(c_168,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_55])).

tff(c_274,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_257,c_39,c_254,c_168])).

tff(c_509,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(k2_pre_topc(A_61,k9_subset_1(u1_struct_0(A_61),B_62,C_63)),k9_subset_1(u1_struct_0(A_61),k2_pre_topc(A_61,B_62),k2_pre_topc(A_61,C_63)))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_536,plain,(
    ! [B_35] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_35,'#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_35),k2_pre_topc('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_509])).

tff(c_604,plain,(
    ! [B_64] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_64,'#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1',B_64),'#skF_2'))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_40,c_257,c_536])).

tff(c_622,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0('#skF_3','#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_604])).

tff(c_633,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_622])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_637,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0('#skF_3','#skF_2')) = k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_633,c_2])).

tff(c_60,plain,(
    ! [B_39] : k9_subset_1(u1_struct_0('#skF_1'),B_39,'#skF_2') = k3_xboole_0(B_39,'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k9_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [B_39] :
      ( m1_subset_1(k3_xboole_0(B_39,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_6])).

tff(c_72,plain,(
    ! [B_39] : m1_subset_1(k3_xboole_0(B_39,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_78,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(B_41,k2_pre_topc(A_42,B_41))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    ! [B_39] :
      ( r1_tarski(k3_xboole_0(B_39,'#skF_2'),k2_pre_topc('#skF_1',k3_xboole_0(B_39,'#skF_2')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_72,c_78])).

tff(c_223,plain,(
    ! [B_49] : r1_tarski(k3_xboole_0(B_49,'#skF_2'),k2_pre_topc('#skF_1',k3_xboole_0(B_49,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_80])).

tff(c_227,plain,(
    ! [B_49] : k3_xboole_0(k3_xboole_0(B_49,'#skF_2'),k2_pre_topc('#skF_1',k3_xboole_0(B_49,'#skF_2'))) = k3_xboole_0(B_49,'#skF_2') ),
    inference(resolution,[status(thm)],[c_223,c_2])).

tff(c_41,plain,(
    ! [B_37] : k9_subset_1(u1_struct_0('#skF_1'),B_37,'#skF_3') = k3_xboole_0(B_37,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_31])).

tff(c_47,plain,(
    ! [B_37] :
      ( m1_subset_1(k3_xboole_0(B_37,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_6])).

tff(c_56,plain,(
    ! [B_38] : m1_subset_1(k3_xboole_0(B_38,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_47])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] :
      ( k9_subset_1(A_9,B_10,C_11) = k3_xboole_0(B_10,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59,plain,(
    ! [B_10,B_38] : k9_subset_1(u1_struct_0('#skF_1'),B_10,k3_xboole_0(B_38,'#skF_3')) = k3_xboole_0(B_10,k3_xboole_0(B_38,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_8])).

tff(c_1016,plain,(
    ! [A_84,B_85,C_86,B_87] :
      ( k9_subset_1(A_84,k9_subset_1(A_84,B_85,C_86),B_87) = k9_subset_1(A_84,B_87,k9_subset_1(A_84,B_85,C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_1036,plain,(
    ! [B_85,B_87] : k9_subset_1(u1_struct_0('#skF_1'),k9_subset_1(u1_struct_0('#skF_1'),B_85,'#skF_3'),B_87) = k9_subset_1(u1_struct_0('#skF_1'),B_87,k9_subset_1(u1_struct_0('#skF_1'),B_85,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_1016])).

tff(c_1051,plain,(
    ! [B_85,B_87] : k9_subset_1(u1_struct_0('#skF_1'),k3_xboole_0(B_85,'#skF_3'),B_87) = k3_xboole_0(B_87,k3_xboole_0(B_85,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_39,c_39,c_1036])).

tff(c_74,plain,(
    ! [B_40] : m1_subset_1(k3_xboole_0(B_40,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_77,plain,(
    ! [B_10,B_40] : k9_subset_1(u1_struct_0('#skF_1'),B_10,k3_xboole_0(B_40,'#skF_2')) = k3_xboole_0(B_10,k3_xboole_0(B_40,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_8])).

tff(c_743,plain,(
    ! [A_70,B_71,B_72,C_73] :
      ( k9_subset_1(A_70,B_71,k9_subset_1(A_70,B_72,C_73)) = k3_xboole_0(B_71,k9_subset_1(A_70,B_72,C_73))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_70)) ) ),
    inference(resolution,[status(thm)],[c_6,c_31])).

tff(c_6797,plain,(
    ! [B_237,C_235,B_239,B_236,A_238] :
      ( k9_subset_1(A_238,B_239,k9_subset_1(A_238,B_236,k9_subset_1(A_238,B_237,C_235))) = k3_xboole_0(B_239,k9_subset_1(A_238,B_236,k9_subset_1(A_238,B_237,C_235)))
      | ~ m1_subset_1(C_235,k1_zfmisc_1(A_238)) ) ),
    inference(resolution,[status(thm)],[c_6,c_743])).

tff(c_6914,plain,(
    ! [B_239,B_236,B_35] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_239,k9_subset_1(u1_struct_0('#skF_1'),B_236,k3_xboole_0(B_35,'#skF_2'))) = k3_xboole_0(B_239,k9_subset_1(u1_struct_0('#skF_1'),B_236,k9_subset_1(u1_struct_0('#skF_1'),B_35,'#skF_2')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6797])).

tff(c_9324,plain,(
    ! [B_288,B_289,B_290] : k9_subset_1(u1_struct_0('#skF_1'),B_288,k3_xboole_0(B_289,k3_xboole_0(B_290,'#skF_2'))) = k3_xboole_0(B_288,k3_xboole_0(B_289,k3_xboole_0(B_290,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_77,c_77,c_40,c_6914])).

tff(c_9411,plain,(
    ! [B_288] : k3_xboole_0(B_288,k3_xboole_0(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0('#skF_3','#skF_2'))) = k9_subset_1(u1_struct_0('#skF_1'),B_288,k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_9324])).

tff(c_16937,plain,(
    ! [B_525] : k9_subset_1(u1_struct_0('#skF_1'),B_525,k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) = k3_xboole_0(B_525,k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_9411])).

tff(c_17454,plain,(
    ! [B_529] : k3_xboole_0(k3_xboole_0(B_529,'#skF_3'),k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) = k3_xboole_0(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(B_529,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_16937])).

tff(c_17557,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_17454])).

tff(c_17575,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_227,c_148,c_17557])).

tff(c_17577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_17575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.21/5.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.21/5.41  
% 13.21/5.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.21/5.41  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 13.21/5.41  
% 13.21/5.41  %Foreground sorts:
% 13.21/5.41  
% 13.21/5.41  
% 13.21/5.41  %Background operators:
% 13.21/5.41  
% 13.21/5.41  
% 13.21/5.41  %Foreground operators:
% 13.21/5.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.21/5.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.21/5.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.21/5.41  tff('#skF_2', type, '#skF_2': $i).
% 13.21/5.41  tff('#skF_3', type, '#skF_3': $i).
% 13.21/5.41  tff('#skF_1', type, '#skF_1': $i).
% 13.21/5.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.21/5.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 13.21/5.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.21/5.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.21/5.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.21/5.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.21/5.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.21/5.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 13.21/5.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 13.21/5.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.21/5.41  
% 13.21/5.43  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_1)).
% 13.21/5.43  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 13.21/5.43  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 13.21/5.43  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 13.21/5.43  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 13.21/5.43  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.21/5.43  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 13.21/5.43  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 13.21/5.43  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.21/5.43  tff(c_31, plain, (![A_34, B_35, C_36]: (k9_subset_1(A_34, B_35, C_36)=k3_xboole_0(B_35, C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.21/5.43  tff(c_40, plain, (![B_35]: (k9_subset_1(u1_struct_0('#skF_1'), B_35, '#skF_2')=k3_xboole_0(B_35, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_31])).
% 13.21/5.43  tff(c_107, plain, (![A_43, C_44, B_45]: (k9_subset_1(A_43, C_44, B_45)=k9_subset_1(A_43, B_45, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.21/5.43  tff(c_117, plain, (![B_45]: (k9_subset_1(u1_struct_0('#skF_1'), B_45, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_45))), inference(resolution, [status(thm)], [c_26, c_107])).
% 13.21/5.43  tff(c_137, plain, (![B_46]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_46)=k3_xboole_0(B_46, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_117])).
% 13.21/5.43  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.21/5.43  tff(c_39, plain, (![B_35]: (k9_subset_1(u1_struct_0('#skF_1'), B_35, '#skF_3')=k3_xboole_0(B_35, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_31])).
% 13.21/5.43  tff(c_148, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_137, c_39])).
% 13.21/5.43  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.21/5.43  tff(c_22, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.21/5.43  tff(c_228, plain, (![A_50, B_51]: (k2_pre_topc(A_50, B_51)=B_51 | ~v4_pre_topc(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.21/5.43  tff(c_244, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_228])).
% 13.21/5.43  tff(c_257, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_244])).
% 13.21/5.43  tff(c_20, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.21/5.43  tff(c_241, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_228])).
% 13.21/5.43  tff(c_254, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20, c_241])).
% 13.21/5.43  tff(c_18, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.21/5.43  tff(c_55, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_18])).
% 13.21/5.43  tff(c_168, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_55])).
% 13.21/5.43  tff(c_274, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_257, c_39, c_254, c_168])).
% 13.21/5.43  tff(c_509, plain, (![A_61, B_62, C_63]: (r1_tarski(k2_pre_topc(A_61, k9_subset_1(u1_struct_0(A_61), B_62, C_63)), k9_subset_1(u1_struct_0(A_61), k2_pre_topc(A_61, B_62), k2_pre_topc(A_61, C_63))) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.21/5.43  tff(c_536, plain, (![B_35]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_35, '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_35), k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_509])).
% 13.21/5.43  tff(c_604, plain, (![B_64]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_64, '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', B_64), '#skF_2')) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_40, c_257, c_536])).
% 13.21/5.43  tff(c_622, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0('#skF_3', '#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_254, c_604])).
% 13.21/5.43  tff(c_633, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_622])).
% 13.21/5.43  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.21/5.43  tff(c_637, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0('#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_633, c_2])).
% 13.21/5.43  tff(c_60, plain, (![B_39]: (k9_subset_1(u1_struct_0('#skF_1'), B_39, '#skF_2')=k3_xboole_0(B_39, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_31])).
% 13.21/5.43  tff(c_6, plain, (![A_6, B_7, C_8]: (m1_subset_1(k9_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.21/5.43  tff(c_66, plain, (![B_39]: (m1_subset_1(k3_xboole_0(B_39, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_60, c_6])).
% 13.21/5.43  tff(c_72, plain, (![B_39]: (m1_subset_1(k3_xboole_0(B_39, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 13.21/5.43  tff(c_78, plain, (![B_41, A_42]: (r1_tarski(B_41, k2_pre_topc(A_42, B_41)) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.21/5.43  tff(c_80, plain, (![B_39]: (r1_tarski(k3_xboole_0(B_39, '#skF_2'), k2_pre_topc('#skF_1', k3_xboole_0(B_39, '#skF_2'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_72, c_78])).
% 13.21/5.43  tff(c_223, plain, (![B_49]: (r1_tarski(k3_xboole_0(B_49, '#skF_2'), k2_pre_topc('#skF_1', k3_xboole_0(B_49, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_80])).
% 13.21/5.43  tff(c_227, plain, (![B_49]: (k3_xboole_0(k3_xboole_0(B_49, '#skF_2'), k2_pre_topc('#skF_1', k3_xboole_0(B_49, '#skF_2')))=k3_xboole_0(B_49, '#skF_2'))), inference(resolution, [status(thm)], [c_223, c_2])).
% 13.21/5.43  tff(c_41, plain, (![B_37]: (k9_subset_1(u1_struct_0('#skF_1'), B_37, '#skF_3')=k3_xboole_0(B_37, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_31])).
% 13.21/5.43  tff(c_47, plain, (![B_37]: (m1_subset_1(k3_xboole_0(B_37, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_41, c_6])).
% 13.21/5.43  tff(c_56, plain, (![B_38]: (m1_subset_1(k3_xboole_0(B_38, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_47])).
% 13.21/5.43  tff(c_8, plain, (![A_9, B_10, C_11]: (k9_subset_1(A_9, B_10, C_11)=k3_xboole_0(B_10, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.21/5.43  tff(c_59, plain, (![B_10, B_38]: (k9_subset_1(u1_struct_0('#skF_1'), B_10, k3_xboole_0(B_38, '#skF_3'))=k3_xboole_0(B_10, k3_xboole_0(B_38, '#skF_3')))), inference(resolution, [status(thm)], [c_56, c_8])).
% 13.21/5.43  tff(c_1016, plain, (![A_84, B_85, C_86, B_87]: (k9_subset_1(A_84, k9_subset_1(A_84, B_85, C_86), B_87)=k9_subset_1(A_84, B_87, k9_subset_1(A_84, B_85, C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)))), inference(resolution, [status(thm)], [c_6, c_107])).
% 13.21/5.43  tff(c_1036, plain, (![B_85, B_87]: (k9_subset_1(u1_struct_0('#skF_1'), k9_subset_1(u1_struct_0('#skF_1'), B_85, '#skF_3'), B_87)=k9_subset_1(u1_struct_0('#skF_1'), B_87, k9_subset_1(u1_struct_0('#skF_1'), B_85, '#skF_3')))), inference(resolution, [status(thm)], [c_24, c_1016])).
% 13.21/5.43  tff(c_1051, plain, (![B_85, B_87]: (k9_subset_1(u1_struct_0('#skF_1'), k3_xboole_0(B_85, '#skF_3'), B_87)=k3_xboole_0(B_87, k3_xboole_0(B_85, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_39, c_39, c_1036])).
% 13.21/5.43  tff(c_74, plain, (![B_40]: (m1_subset_1(k3_xboole_0(B_40, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 13.21/5.43  tff(c_77, plain, (![B_10, B_40]: (k9_subset_1(u1_struct_0('#skF_1'), B_10, k3_xboole_0(B_40, '#skF_2'))=k3_xboole_0(B_10, k3_xboole_0(B_40, '#skF_2')))), inference(resolution, [status(thm)], [c_74, c_8])).
% 13.21/5.43  tff(c_743, plain, (![A_70, B_71, B_72, C_73]: (k9_subset_1(A_70, B_71, k9_subset_1(A_70, B_72, C_73))=k3_xboole_0(B_71, k9_subset_1(A_70, B_72, C_73)) | ~m1_subset_1(C_73, k1_zfmisc_1(A_70)))), inference(resolution, [status(thm)], [c_6, c_31])).
% 13.21/5.43  tff(c_6797, plain, (![B_237, C_235, B_239, B_236, A_238]: (k9_subset_1(A_238, B_239, k9_subset_1(A_238, B_236, k9_subset_1(A_238, B_237, C_235)))=k3_xboole_0(B_239, k9_subset_1(A_238, B_236, k9_subset_1(A_238, B_237, C_235))) | ~m1_subset_1(C_235, k1_zfmisc_1(A_238)))), inference(resolution, [status(thm)], [c_6, c_743])).
% 13.21/5.43  tff(c_6914, plain, (![B_239, B_236, B_35]: (k9_subset_1(u1_struct_0('#skF_1'), B_239, k9_subset_1(u1_struct_0('#skF_1'), B_236, k3_xboole_0(B_35, '#skF_2')))=k3_xboole_0(B_239, k9_subset_1(u1_struct_0('#skF_1'), B_236, k9_subset_1(u1_struct_0('#skF_1'), B_35, '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_40, c_6797])).
% 13.21/5.43  tff(c_9324, plain, (![B_288, B_289, B_290]: (k9_subset_1(u1_struct_0('#skF_1'), B_288, k3_xboole_0(B_289, k3_xboole_0(B_290, '#skF_2')))=k3_xboole_0(B_288, k3_xboole_0(B_289, k3_xboole_0(B_290, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_77, c_77, c_40, c_6914])).
% 13.21/5.43  tff(c_9411, plain, (![B_288]: (k3_xboole_0(B_288, k3_xboole_0(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0('#skF_3', '#skF_2')))=k9_subset_1(u1_struct_0('#skF_1'), B_288, k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_637, c_9324])).
% 13.21/5.43  tff(c_16937, plain, (![B_525]: (k9_subset_1(u1_struct_0('#skF_1'), B_525, k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))=k3_xboole_0(B_525, k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_9411])).
% 13.21/5.43  tff(c_17454, plain, (![B_529]: (k3_xboole_0(k3_xboole_0(B_529, '#skF_3'), k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))=k3_xboole_0(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(B_529, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1051, c_16937])).
% 13.21/5.43  tff(c_17557, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_17454])).
% 13.21/5.43  tff(c_17575, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_637, c_227, c_148, c_17557])).
% 13.21/5.43  tff(c_17577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_17575])).
% 13.21/5.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.21/5.43  
% 13.21/5.43  Inference rules
% 13.21/5.43  ----------------------
% 13.21/5.43  #Ref     : 0
% 13.21/5.43  #Sup     : 4855
% 13.21/5.43  #Fact    : 0
% 13.21/5.43  #Define  : 0
% 13.21/5.43  #Split   : 1
% 13.21/5.43  #Chain   : 0
% 13.21/5.43  #Close   : 0
% 13.21/5.43  
% 13.21/5.43  Ordering : KBO
% 13.21/5.43  
% 13.21/5.43  Simplification rules
% 13.21/5.43  ----------------------
% 13.21/5.43  #Subsume      : 217
% 13.21/5.43  #Demod        : 3555
% 13.21/5.43  #Tautology    : 1153
% 13.21/5.43  #SimpNegUnit  : 2
% 13.21/5.43  #BackRed      : 5
% 13.21/5.43  
% 13.21/5.43  #Partial instantiations: 0
% 13.21/5.43  #Strategies tried      : 1
% 13.21/5.43  
% 13.21/5.43  Timing (in seconds)
% 13.21/5.43  ----------------------
% 13.21/5.43  Preprocessing        : 0.37
% 13.21/5.43  Parsing              : 0.19
% 13.21/5.43  CNF conversion       : 0.03
% 13.21/5.43  Main loop            : 4.20
% 13.21/5.43  Inferencing          : 0.80
% 13.21/5.43  Reduction            : 2.34
% 13.21/5.43  Demodulation         : 2.06
% 13.21/5.43  BG Simplification    : 0.15
% 13.21/5.43  Subsumption          : 0.66
% 13.21/5.43  Abstraction          : 0.24
% 13.21/5.43  MUC search           : 0.00
% 13.21/5.43  Cooper               : 0.00
% 13.21/5.43  Total                : 4.61
% 13.21/5.43  Index Insertion      : 0.00
% 13.21/5.43  Index Deletion       : 0.00
% 13.21/5.43  Index Matching       : 0.00
% 13.21/5.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
