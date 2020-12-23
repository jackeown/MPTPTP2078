%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:50 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 242 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  216 ( 729 expanded)
%              Number of equality atoms :   32 (  99 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_220,plain,(
    ! [B_71,A_72] :
      ( v2_tops_1(B_71,A_72)
      | k1_tops_1(A_72,B_71) != k1_xboole_0
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_227,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_220])).

tff(c_231,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_227])).

tff(c_232,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_231])).

tff(c_151,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_tops_1(A_65,B_66),B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_151])).

tff(c_160,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_156])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_161,plain,(
    ! [A_67,B_68] :
      ( v3_pre_topc(k1_tops_1(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_166,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_161])).

tff(c_170,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_166])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_95,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_61,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_63,c_95])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    ! [A_3,A_61] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_61)
      | ~ r1_tarski(A_61,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_172,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_123])).

tff(c_179,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_172])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [C_46] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_46
      | ~ v3_pre_topc(C_46,'#skF_1')
      | ~ r1_tarski(C_46,'#skF_2')
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_272,plain,(
    ! [C_76] :
      ( k1_xboole_0 = C_76
      | ~ v3_pre_topc(C_76,'#skF_1')
      | ~ r1_tarski(C_76,'#skF_2')
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54])).

tff(c_396,plain,(
    ! [A_88] :
      ( k1_xboole_0 = A_88
      | ~ v3_pre_topc(A_88,'#skF_1')
      | ~ r1_tarski(A_88,'#skF_2')
      | ~ r1_tarski(A_88,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_272])).

tff(c_407,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_396])).

tff(c_426,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_170,c_407])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_426])).

tff(c_429,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_430,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_432,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_40])).

tff(c_38,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_434,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_38])).

tff(c_42,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_441,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_42])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_537,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(k1_tops_1(A_104,B_105),B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_895,plain,(
    ! [A_125,A_126] :
      ( r1_tarski(k1_tops_1(A_125,A_126),A_126)
      | ~ l1_pre_topc(A_125)
      | ~ r1_tarski(A_126,u1_struct_0(A_125)) ) ),
    inference(resolution,[status(thm)],[c_14,c_537])).

tff(c_451,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_469,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_451])).

tff(c_920,plain,(
    ! [A_125] :
      ( k1_tops_1(A_125,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_125)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_125)) ) ),
    inference(resolution,[status(thm)],[c_895,c_469])).

tff(c_944,plain,(
    ! [A_127] :
      ( k1_tops_1(A_127,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_920])).

tff(c_948,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_944])).

tff(c_1003,plain,(
    ! [A_130,B_131,C_132] :
      ( r1_tarski(k1_tops_1(A_130,B_131),k1_tops_1(A_130,C_132))
      | ~ r1_tarski(B_131,C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1031,plain,(
    ! [B_131] :
      ( r1_tarski(k1_tops_1('#skF_1',B_131),k1_xboole_0)
      | ~ r1_tarski(B_131,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_1003])).

tff(c_1055,plain,(
    ! [B_131] :
      ( r1_tarski(k1_tops_1('#skF_1',B_131),k1_xboole_0)
      | ~ r1_tarski(B_131,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1031])).

tff(c_1123,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1055])).

tff(c_1126,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_1123])).

tff(c_1130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1126])).

tff(c_1132,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1055])).

tff(c_24,plain,(
    ! [B_29,D_35,C_33,A_21] :
      ( k1_tops_1(B_29,D_35) = D_35
      | ~ v3_pre_topc(D_35,B_29)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0(B_29)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1162,plain,(
    ! [C_140,A_141] :
      ( ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_1165,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1132,c_1162])).

tff(c_1179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1165])).

tff(c_1261,plain,(
    ! [B_150,D_151] :
      ( k1_tops_1(B_150,D_151) = D_151
      | ~ v3_pre_topc(D_151,B_150)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0(B_150)))
      | ~ l1_pre_topc(B_150) ) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1271,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_441,c_1261])).

tff(c_1281,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_434,c_1271])).

tff(c_542,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_441,c_537])).

tff(c_548,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_542])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_557,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_548,c_2])).

tff(c_695,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_1291,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1281,c_695])).

tff(c_1301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1291])).

tff(c_1302,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_1599,plain,(
    ! [A_169,B_170] :
      ( k1_tops_1(A_169,B_170) = k1_xboole_0
      | ~ v2_tops_1(B_170,A_169)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1609,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1599])).

tff(c_1617,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_430,c_1609])).

tff(c_1747,plain,(
    ! [A_179,B_180,C_181] :
      ( r1_tarski(k1_tops_1(A_179,B_180),k1_tops_1(A_179,C_181))
      | ~ r1_tarski(B_180,C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1770,plain,(
    ! [B_180] :
      ( r1_tarski(k1_tops_1('#skF_1',B_180),k1_xboole_0)
      | ~ r1_tarski(B_180,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_1747])).

tff(c_1990,plain,(
    ! [B_192] :
      ( r1_tarski(k1_tops_1('#skF_1',B_192),k1_xboole_0)
      | ~ r1_tarski(B_192,'#skF_2')
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1770])).

tff(c_2000,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_441,c_1990])).

tff(c_2010,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_1302,c_2000])).

tff(c_2024,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2010,c_469])).

tff(c_2042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_2024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:06:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.73  
% 3.71/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.73  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.71/1.73  
% 3.71/1.73  %Foreground sorts:
% 3.71/1.73  
% 3.71/1.73  
% 3.71/1.73  %Background operators:
% 3.71/1.73  
% 3.71/1.73  
% 3.71/1.73  %Foreground operators:
% 3.71/1.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.71/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.71/1.73  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.71/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.71/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.73  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.71/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.71/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.71/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.71/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.73  
% 3.71/1.75  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.71/1.75  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.71/1.75  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.71/1.75  tff(f_51, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.71/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.71/1.75  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.71/1.75  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.71/1.75  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.71/1.75  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 3.71/1.75  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 3.71/1.75  tff(c_36, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.71/1.75  tff(c_58, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.71/1.75  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.71/1.75  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.71/1.75  tff(c_220, plain, (![B_71, A_72]: (v2_tops_1(B_71, A_72) | k1_tops_1(A_72, B_71)!=k1_xboole_0 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.71/1.75  tff(c_227, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_220])).
% 3.71/1.75  tff(c_231, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_227])).
% 3.71/1.75  tff(c_232, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_231])).
% 3.71/1.75  tff(c_151, plain, (![A_65, B_66]: (r1_tarski(k1_tops_1(A_65, B_66), B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.71/1.75  tff(c_156, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_151])).
% 3.71/1.75  tff(c_160, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_156])).
% 3.71/1.75  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.71/1.75  tff(c_161, plain, (![A_67, B_68]: (v3_pre_topc(k1_tops_1(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.71/1.75  tff(c_166, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_161])).
% 3.71/1.75  tff(c_170, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_166])).
% 3.71/1.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.71/1.75  tff(c_59, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.71/1.75  tff(c_63, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_59])).
% 3.71/1.75  tff(c_95, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.71/1.75  tff(c_118, plain, (![A_61]: (r1_tarski(A_61, u1_struct_0('#skF_1')) | ~r1_tarski(A_61, '#skF_2'))), inference(resolution, [status(thm)], [c_63, c_95])).
% 3.71/1.75  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.71/1.75  tff(c_123, plain, (![A_3, A_61]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_61) | ~r1_tarski(A_61, '#skF_2'))), inference(resolution, [status(thm)], [c_118, c_8])).
% 3.71/1.75  tff(c_172, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_160, c_123])).
% 3.71/1.75  tff(c_179, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_172])).
% 3.71/1.75  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.71/1.75  tff(c_54, plain, (![C_46]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_46 | ~v3_pre_topc(C_46, '#skF_1') | ~r1_tarski(C_46, '#skF_2') | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.71/1.75  tff(c_272, plain, (![C_76]: (k1_xboole_0=C_76 | ~v3_pre_topc(C_76, '#skF_1') | ~r1_tarski(C_76, '#skF_2') | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_54])).
% 3.71/1.75  tff(c_396, plain, (![A_88]: (k1_xboole_0=A_88 | ~v3_pre_topc(A_88, '#skF_1') | ~r1_tarski(A_88, '#skF_2') | ~r1_tarski(A_88, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_272])).
% 3.71/1.75  tff(c_407, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_179, c_396])).
% 3.71/1.75  tff(c_426, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_160, c_170, c_407])).
% 3.71/1.75  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_426])).
% 3.71/1.75  tff(c_429, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.71/1.75  tff(c_430, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.71/1.75  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.71/1.75  tff(c_432, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_40])).
% 3.71/1.75  tff(c_38, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.71/1.75  tff(c_434, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_38])).
% 3.71/1.75  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.71/1.75  tff(c_441, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_42])).
% 3.71/1.75  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.71/1.75  tff(c_537, plain, (![A_104, B_105]: (r1_tarski(k1_tops_1(A_104, B_105), B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.71/1.75  tff(c_895, plain, (![A_125, A_126]: (r1_tarski(k1_tops_1(A_125, A_126), A_126) | ~l1_pre_topc(A_125) | ~r1_tarski(A_126, u1_struct_0(A_125)))), inference(resolution, [status(thm)], [c_14, c_537])).
% 3.71/1.75  tff(c_451, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.71/1.75  tff(c_469, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_451])).
% 3.71/1.75  tff(c_920, plain, (![A_125]: (k1_tops_1(A_125, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_125) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_125)))), inference(resolution, [status(thm)], [c_895, c_469])).
% 3.71/1.75  tff(c_944, plain, (![A_127]: (k1_tops_1(A_127, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_920])).
% 3.71/1.75  tff(c_948, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_944])).
% 3.71/1.75  tff(c_1003, plain, (![A_130, B_131, C_132]: (r1_tarski(k1_tops_1(A_130, B_131), k1_tops_1(A_130, C_132)) | ~r1_tarski(B_131, C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.75  tff(c_1031, plain, (![B_131]: (r1_tarski(k1_tops_1('#skF_1', B_131), k1_xboole_0) | ~r1_tarski(B_131, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_948, c_1003])).
% 3.71/1.75  tff(c_1055, plain, (![B_131]: (r1_tarski(k1_tops_1('#skF_1', B_131), k1_xboole_0) | ~r1_tarski(B_131, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1031])).
% 3.71/1.75  tff(c_1123, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1055])).
% 3.71/1.75  tff(c_1126, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_1123])).
% 3.71/1.75  tff(c_1130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1126])).
% 3.71/1.75  tff(c_1132, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1055])).
% 3.71/1.75  tff(c_24, plain, (![B_29, D_35, C_33, A_21]: (k1_tops_1(B_29, D_35)=D_35 | ~v3_pre_topc(D_35, B_29) | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0(B_29))) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.71/1.75  tff(c_1162, plain, (![C_140, A_141]: (~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(splitLeft, [status(thm)], [c_24])).
% 3.71/1.75  tff(c_1165, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1132, c_1162])).
% 3.71/1.75  tff(c_1179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1165])).
% 3.71/1.75  tff(c_1261, plain, (![B_150, D_151]: (k1_tops_1(B_150, D_151)=D_151 | ~v3_pre_topc(D_151, B_150) | ~m1_subset_1(D_151, k1_zfmisc_1(u1_struct_0(B_150))) | ~l1_pre_topc(B_150))), inference(splitRight, [status(thm)], [c_24])).
% 3.71/1.75  tff(c_1271, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_441, c_1261])).
% 3.71/1.75  tff(c_1281, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_434, c_1271])).
% 3.71/1.75  tff(c_542, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_441, c_537])).
% 3.71/1.75  tff(c_548, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_542])).
% 3.71/1.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.71/1.75  tff(c_557, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_548, c_2])).
% 3.71/1.75  tff(c_695, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_557])).
% 3.71/1.75  tff(c_1291, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1281, c_695])).
% 3.71/1.75  tff(c_1301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1291])).
% 3.71/1.75  tff(c_1302, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_557])).
% 3.71/1.75  tff(c_1599, plain, (![A_169, B_170]: (k1_tops_1(A_169, B_170)=k1_xboole_0 | ~v2_tops_1(B_170, A_169) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.71/1.75  tff(c_1609, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1599])).
% 3.71/1.75  tff(c_1617, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_430, c_1609])).
% 3.71/1.75  tff(c_1747, plain, (![A_179, B_180, C_181]: (r1_tarski(k1_tops_1(A_179, B_180), k1_tops_1(A_179, C_181)) | ~r1_tarski(B_180, C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.75  tff(c_1770, plain, (![B_180]: (r1_tarski(k1_tops_1('#skF_1', B_180), k1_xboole_0) | ~r1_tarski(B_180, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1617, c_1747])).
% 3.71/1.75  tff(c_1990, plain, (![B_192]: (r1_tarski(k1_tops_1('#skF_1', B_192), k1_xboole_0) | ~r1_tarski(B_192, '#skF_2') | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1770])).
% 3.71/1.75  tff(c_2000, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_441, c_1990])).
% 3.71/1.75  tff(c_2010, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_432, c_1302, c_2000])).
% 3.71/1.75  tff(c_2024, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2010, c_469])).
% 3.71/1.75  tff(c_2042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_2024])).
% 3.71/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.75  
% 3.71/1.75  Inference rules
% 3.71/1.75  ----------------------
% 3.71/1.75  #Ref     : 0
% 3.71/1.75  #Sup     : 407
% 3.71/1.75  #Fact    : 0
% 3.71/1.75  #Define  : 0
% 3.71/1.75  #Split   : 19
% 3.71/1.75  #Chain   : 0
% 3.71/1.75  #Close   : 0
% 3.71/1.75  
% 3.71/1.75  Ordering : KBO
% 3.71/1.75  
% 3.71/1.75  Simplification rules
% 3.71/1.75  ----------------------
% 3.71/1.75  #Subsume      : 147
% 3.71/1.75  #Demod        : 336
% 3.71/1.75  #Tautology    : 119
% 3.71/1.75  #SimpNegUnit  : 10
% 3.71/1.75  #BackRed      : 24
% 3.71/1.75  
% 3.71/1.75  #Partial instantiations: 0
% 3.71/1.75  #Strategies tried      : 1
% 3.71/1.75  
% 3.71/1.75  Timing (in seconds)
% 3.71/1.75  ----------------------
% 3.71/1.75  Preprocessing        : 0.34
% 3.71/1.75  Parsing              : 0.18
% 3.71/1.75  CNF conversion       : 0.02
% 3.71/1.75  Main loop            : 0.51
% 3.71/1.75  Inferencing          : 0.17
% 3.71/1.75  Reduction            : 0.17
% 3.71/1.75  Demodulation         : 0.12
% 3.71/1.75  BG Simplification    : 0.02
% 3.71/1.75  Subsumption          : 0.11
% 3.71/1.75  Abstraction          : 0.02
% 3.71/1.75  MUC search           : 0.00
% 3.71/1.75  Cooper               : 0.00
% 3.71/1.75  Total                : 0.89
% 3.71/1.75  Index Insertion      : 0.00
% 3.71/1.75  Index Deletion       : 0.00
% 3.71/1.75  Index Matching       : 0.00
% 3.71/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
