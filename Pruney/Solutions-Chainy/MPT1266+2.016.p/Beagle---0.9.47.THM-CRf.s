%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:45 EST 2020

% Result     : Theorem 8.91s
% Output     : CNFRefutation 9.03s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 959 expanded)
%              Number of leaves         :   33 ( 334 expanded)
%              Depth                    :   15
%              Number of atoms          :  236 (2054 expanded)
%              Number of equality atoms :   62 ( 556 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_27,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_36,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_82,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_72,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_77,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_81,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_83,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_32])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_269,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,B_59) = k2_struct_0(A_58)
      | ~ v1_tops_1(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_283,plain,(
    ! [B_59] :
      ( k2_pre_topc('#skF_1',B_59) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_59,'#skF_1')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_269])).

tff(c_343,plain,(
    ! [B_66] :
      ( k2_pre_topc('#skF_1',B_66) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_66,'#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_283])).

tff(c_366,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_83,c_343])).

tff(c_368,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_116,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_83,c_116])).

tff(c_376,plain,(
    ! [A_67,B_68] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_67),B_68),A_67)
      | ~ v2_tops_1(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_387,plain,(
    ! [B_68] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_68),'#skF_1')
      | ~ v2_tops_1(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_376])).

tff(c_591,plain,(
    ! [B_82] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_82),'#skF_1')
      | ~ v2_tops_1(B_82,'#skF_1')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81,c_387])).

tff(c_604,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_591])).

tff(c_614,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_604])).

tff(c_621,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_614])).

tff(c_624,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_621])).

tff(c_628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_624])).

tff(c_630,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_614])).

tff(c_292,plain,(
    ! [B_59] :
      ( k2_pre_topc('#skF_1',B_59) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_59,'#skF_1')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_283])).

tff(c_642,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_630,c_292])).

tff(c_866,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_642])).

tff(c_302,plain,(
    ! [B_62,A_63] :
      ( v1_tops_1(B_62,A_63)
      | k2_pre_topc(A_63,B_62) != k2_struct_0(A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_316,plain,(
    ! [B_62] :
      ( v1_tops_1(B_62,'#skF_1')
      | k2_pre_topc('#skF_1',B_62) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_302])).

tff(c_325,plain,(
    ! [B_62] :
      ( v1_tops_1(B_62,'#skF_1')
      | k2_pre_topc('#skF_1',B_62) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_316])).

tff(c_641,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_630,c_325])).

tff(c_878,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_641])).

tff(c_2,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_44,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_42,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_88,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_42])).

tff(c_22,plain,(
    ! [A_16,B_18] :
      ( k3_subset_1(u1_struct_0(A_16),k2_pre_topc(A_16,k3_subset_1(u1_struct_0(A_16),B_18))) = k1_tops_1(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k2_pre_topc(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,B_6)) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1196,plain,(
    ! [A_103,B_104] :
      ( k3_subset_1(u1_struct_0(A_103),k3_subset_1(u1_struct_0(A_103),k2_pre_topc(A_103,B_104))) = k2_pre_topc(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_175,c_8])).

tff(c_7072,plain,(
    ! [A_274,B_275] :
      ( k3_subset_1(u1_struct_0(A_274),k1_tops_1(A_274,B_275)) = k2_pre_topc(A_274,k3_subset_1(u1_struct_0(A_274),B_275))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_274),B_275),k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1196])).

tff(c_7135,plain,(
    ! [B_275] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_275)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_275))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_275),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_7072])).

tff(c_7152,plain,(
    ! [B_276] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_276)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_276))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_276),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81,c_34,c_81,c_81,c_81,c_7135])).

tff(c_7203,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_630,c_7152])).

tff(c_7256,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_44,c_88,c_7203])).

tff(c_7258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_7256])).

tff(c_7260,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_642])).

tff(c_503,plain,(
    ! [B_76,A_77] :
      ( v2_tops_1(B_76,A_77)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_77),B_76),A_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_517,plain,(
    ! [B_76] :
      ( v2_tops_1(B_76,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_76),'#skF_1')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_503])).

tff(c_526,plain,(
    ! [B_76] :
      ( v2_tops_1(B_76,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_76),'#skF_1')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81,c_517])).

tff(c_7263,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7260,c_526])).

tff(c_7266,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_7263])).

tff(c_7268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7266])).

tff(c_7269,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_7271,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_32])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7285,plain,(
    ! [A_280,B_281] :
      ( k3_subset_1(A_280,k3_subset_1(A_280,B_281)) = B_281
      | ~ m1_subset_1(B_281,k1_zfmisc_1(A_280)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7293,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_7285])).

tff(c_7298,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7293])).

tff(c_7270,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_7631,plain,(
    ! [A_317,B_318] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_317),B_318),A_317)
      | ~ v2_tops_1(B_318,A_317)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ l1_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7645,plain,(
    ! [B_318] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_318),'#skF_1')
      | ~ v2_tops_1(B_318,'#skF_1')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_7631])).

tff(c_7654,plain,(
    ! [B_318] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_318),'#skF_1')
      | ~ v2_tops_1(B_318,'#skF_1')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81,c_7645])).

tff(c_7431,plain,(
    ! [B_301,A_302] :
      ( v1_tops_1(B_301,A_302)
      | k2_pre_topc(A_302,B_301) != k2_struct_0(A_302)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7445,plain,(
    ! [B_301] :
      ( v1_tops_1(B_301,'#skF_1')
      | k2_pre_topc('#skF_1',B_301) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_301,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_7431])).

tff(c_7505,plain,(
    ! [B_309] :
      ( v1_tops_1(B_309,'#skF_1')
      | k2_pre_topc('#skF_1',B_309) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_309,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7445])).

tff(c_7527,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7271,c_7505])).

tff(c_7530,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7527])).

tff(c_7464,plain,(
    ! [A_305,B_306] :
      ( k2_pre_topc(A_305,B_306) = k2_struct_0(A_305)
      | ~ v1_tops_1(B_306,A_305)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7478,plain,(
    ! [B_306] :
      ( k2_pre_topc('#skF_1',B_306) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_306,'#skF_1')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_7464])).

tff(c_7570,plain,(
    ! [B_314] :
      ( k2_pre_topc('#skF_1',B_314) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_314,'#skF_1')
      | ~ m1_subset_1(B_314,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7478])).

tff(c_7584,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_7271,c_7570])).

tff(c_7595,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_7530,c_7584])).

tff(c_7296,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7271,c_7285])).

tff(c_7683,plain,(
    ! [B_321] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_321),'#skF_1')
      | ~ v2_tops_1(B_321,'#skF_1')
      | ~ m1_subset_1(B_321,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81,c_7645])).

tff(c_7697,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7296,c_7683])).

tff(c_7706,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7595,c_7697])).

tff(c_7990,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7706])).

tff(c_7993,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_7990])).

tff(c_7997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7271,c_7993])).

tff(c_7999,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7706])).

tff(c_7487,plain,(
    ! [B_306] :
      ( k2_pre_topc('#skF_1',B_306) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_306,'#skF_1')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7478])).

tff(c_8015,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7999,c_7487])).

tff(c_8021,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8015])).

tff(c_8024,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7654,c_8021])).

tff(c_8028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7271,c_7270,c_8024])).

tff(c_8029,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8015])).

tff(c_7766,plain,(
    ! [A_326,B_327] :
      ( k3_subset_1(u1_struct_0(A_326),k2_pre_topc(A_326,k3_subset_1(u1_struct_0(A_326),B_327))) = k1_tops_1(A_326,B_327)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ l1_pre_topc(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7807,plain,(
    ! [B_327] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_327))) = k1_tops_1('#skF_1',B_327)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_7766])).

tff(c_7819,plain,(
    ! [B_327] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_327))) = k1_tops_1('#skF_1',B_327)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81,c_81,c_7807])).

tff(c_8042,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8029,c_7819])).

tff(c_8056,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7271,c_7298,c_8042])).

tff(c_8058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7269,c_8056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.91/2.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.00  
% 8.91/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.91/3.00  %$ v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.91/3.00  
% 8.91/3.00  %Foreground sorts:
% 8.91/3.00  
% 8.91/3.00  
% 8.91/3.00  %Background operators:
% 8.91/3.00  
% 8.91/3.00  
% 8.91/3.00  %Foreground operators:
% 8.91/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.91/3.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.91/3.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.91/3.00  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 8.91/3.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.91/3.00  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.91/3.00  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 8.91/3.00  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.91/3.00  tff('#skF_2', type, '#skF_2': $i).
% 8.91/3.00  tff('#skF_1', type, '#skF_1': $i).
% 8.91/3.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.91/3.00  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.91/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.91/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.91/3.00  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 8.91/3.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.91/3.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.91/3.00  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.91/3.00  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.91/3.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.91/3.00  
% 9.03/3.02  tff(f_96, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 9.03/3.02  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.03/3.02  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 9.03/3.02  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.03/3.02  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 9.03/3.02  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.03/3.02  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 9.03/3.02  tff(f_27, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 9.03/3.02  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 9.03/3.02  tff(f_39, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 9.03/3.02  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 9.03/3.02  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.03/3.02  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.03/3.02  tff(c_36, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.03/3.02  tff(c_82, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 9.03/3.02  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.03/3.02  tff(c_20, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.03/3.02  tff(c_72, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.03/3.02  tff(c_77, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_20, c_72])).
% 9.03/3.02  tff(c_81, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_77])).
% 9.03/3.02  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.03/3.02  tff(c_83, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_32])).
% 9.03/3.02  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.03/3.02  tff(c_269, plain, (![A_58, B_59]: (k2_pre_topc(A_58, B_59)=k2_struct_0(A_58) | ~v1_tops_1(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.03/3.02  tff(c_283, plain, (![B_59]: (k2_pre_topc('#skF_1', B_59)=k2_struct_0('#skF_1') | ~v1_tops_1(B_59, '#skF_1') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_269])).
% 9.03/3.02  tff(c_343, plain, (![B_66]: (k2_pre_topc('#skF_1', B_66)=k2_struct_0('#skF_1') | ~v1_tops_1(B_66, '#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_283])).
% 9.03/3.02  tff(c_366, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_83, c_343])).
% 9.03/3.02  tff(c_368, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_366])).
% 9.03/3.02  tff(c_116, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.03/3.02  tff(c_127, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_83, c_116])).
% 9.03/3.02  tff(c_376, plain, (![A_67, B_68]: (v1_tops_1(k3_subset_1(u1_struct_0(A_67), B_68), A_67) | ~v2_tops_1(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.03/3.02  tff(c_387, plain, (![B_68]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_68), '#skF_1') | ~v2_tops_1(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_376])).
% 9.03/3.02  tff(c_591, plain, (![B_82]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_82), '#skF_1') | ~v2_tops_1(B_82, '#skF_1') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81, c_387])).
% 9.03/3.02  tff(c_604, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_127, c_591])).
% 9.03/3.02  tff(c_614, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_368, c_604])).
% 9.03/3.02  tff(c_621, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_614])).
% 9.03/3.02  tff(c_624, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_621])).
% 9.03/3.02  tff(c_628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_624])).
% 9.03/3.02  tff(c_630, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_614])).
% 9.03/3.02  tff(c_292, plain, (![B_59]: (k2_pre_topc('#skF_1', B_59)=k2_struct_0('#skF_1') | ~v1_tops_1(B_59, '#skF_1') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_283])).
% 9.03/3.02  tff(c_642, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_630, c_292])).
% 9.03/3.02  tff(c_866, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_642])).
% 9.03/3.02  tff(c_302, plain, (![B_62, A_63]: (v1_tops_1(B_62, A_63) | k2_pre_topc(A_63, B_62)!=k2_struct_0(A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.03/3.02  tff(c_316, plain, (![B_62]: (v1_tops_1(B_62, '#skF_1') | k2_pre_topc('#skF_1', B_62)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_302])).
% 9.03/3.02  tff(c_325, plain, (![B_62]: (v1_tops_1(B_62, '#skF_1') | k2_pre_topc('#skF_1', B_62)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_316])).
% 9.03/3.02  tff(c_641, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_630, c_325])).
% 9.03/3.02  tff(c_878, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_866, c_641])).
% 9.03/3.02  tff(c_2, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.03/3.02  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.03/3.02  tff(c_10, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.03/3.02  tff(c_43, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 9.03/3.02  tff(c_44, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_43])).
% 9.03/3.02  tff(c_42, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.03/3.02  tff(c_88, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_42])).
% 9.03/3.02  tff(c_22, plain, (![A_16, B_18]: (k3_subset_1(u1_struct_0(A_16), k2_pre_topc(A_16, k3_subset_1(u1_struct_0(A_16), B_18)))=k1_tops_1(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.03/3.02  tff(c_175, plain, (![A_50, B_51]: (m1_subset_1(k2_pre_topc(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.03/3.02  tff(c_8, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, B_6))=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.03/3.02  tff(c_1196, plain, (![A_103, B_104]: (k3_subset_1(u1_struct_0(A_103), k3_subset_1(u1_struct_0(A_103), k2_pre_topc(A_103, B_104)))=k2_pre_topc(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_175, c_8])).
% 9.03/3.02  tff(c_7072, plain, (![A_274, B_275]: (k3_subset_1(u1_struct_0(A_274), k1_tops_1(A_274, B_275))=k2_pre_topc(A_274, k3_subset_1(u1_struct_0(A_274), B_275)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_274), B_275), k1_zfmisc_1(u1_struct_0(A_274))) | ~l1_pre_topc(A_274) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0(A_274))) | ~l1_pre_topc(A_274))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1196])).
% 9.03/3.02  tff(c_7135, plain, (![B_275]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_275))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_275)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_275), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_7072])).
% 9.03/3.02  tff(c_7152, plain, (![B_276]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_276))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_276)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_276), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_276, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81, c_34, c_81, c_81, c_81, c_7135])).
% 9.03/3.02  tff(c_7203, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_630, c_7152])).
% 9.03/3.02  tff(c_7256, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_44, c_88, c_7203])).
% 9.03/3.02  tff(c_7258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_7256])).
% 9.03/3.02  tff(c_7260, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_642])).
% 9.03/3.02  tff(c_503, plain, (![B_76, A_77]: (v2_tops_1(B_76, A_77) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_77), B_76), A_77) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.03/3.02  tff(c_517, plain, (![B_76]: (v2_tops_1(B_76, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_76), '#skF_1') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_503])).
% 9.03/3.02  tff(c_526, plain, (![B_76]: (v2_tops_1(B_76, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_76), '#skF_1') | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81, c_517])).
% 9.03/3.02  tff(c_7263, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7260, c_526])).
% 9.03/3.02  tff(c_7266, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_7263])).
% 9.03/3.02  tff(c_7268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_7266])).
% 9.03/3.02  tff(c_7269, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 9.03/3.02  tff(c_7271, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_32])).
% 9.03/3.02  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.03/3.02  tff(c_7285, plain, (![A_280, B_281]: (k3_subset_1(A_280, k3_subset_1(A_280, B_281))=B_281 | ~m1_subset_1(B_281, k1_zfmisc_1(A_280)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.03/3.02  tff(c_7293, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_7285])).
% 9.03/3.02  tff(c_7298, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7293])).
% 9.03/3.02  tff(c_7270, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 9.03/3.02  tff(c_7631, plain, (![A_317, B_318]: (v1_tops_1(k3_subset_1(u1_struct_0(A_317), B_318), A_317) | ~v2_tops_1(B_318, A_317) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(A_317))) | ~l1_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.03/3.02  tff(c_7645, plain, (![B_318]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_318), '#skF_1') | ~v2_tops_1(B_318, '#skF_1') | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_7631])).
% 9.03/3.02  tff(c_7654, plain, (![B_318]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_318), '#skF_1') | ~v2_tops_1(B_318, '#skF_1') | ~m1_subset_1(B_318, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81, c_7645])).
% 9.03/3.02  tff(c_7431, plain, (![B_301, A_302]: (v1_tops_1(B_301, A_302) | k2_pre_topc(A_302, B_301)!=k2_struct_0(A_302) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_302))) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.03/3.02  tff(c_7445, plain, (![B_301]: (v1_tops_1(B_301, '#skF_1') | k2_pre_topc('#skF_1', B_301)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_301, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_7431])).
% 9.03/3.02  tff(c_7505, plain, (![B_309]: (v1_tops_1(B_309, '#skF_1') | k2_pre_topc('#skF_1', B_309)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_309, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7445])).
% 9.03/3.02  tff(c_7527, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_7271, c_7505])).
% 9.03/3.02  tff(c_7530, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_7527])).
% 9.03/3.02  tff(c_7464, plain, (![A_305, B_306]: (k2_pre_topc(A_305, B_306)=k2_struct_0(A_305) | ~v1_tops_1(B_306, A_305) | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.03/3.02  tff(c_7478, plain, (![B_306]: (k2_pre_topc('#skF_1', B_306)=k2_struct_0('#skF_1') | ~v1_tops_1(B_306, '#skF_1') | ~m1_subset_1(B_306, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_7464])).
% 9.03/3.02  tff(c_7570, plain, (![B_314]: (k2_pre_topc('#skF_1', B_314)=k2_struct_0('#skF_1') | ~v1_tops_1(B_314, '#skF_1') | ~m1_subset_1(B_314, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7478])).
% 9.03/3.02  tff(c_7584, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_7271, c_7570])).
% 9.03/3.02  tff(c_7595, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_7530, c_7584])).
% 9.03/3.02  tff(c_7296, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_7271, c_7285])).
% 9.03/3.02  tff(c_7683, plain, (![B_321]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_321), '#skF_1') | ~v2_tops_1(B_321, '#skF_1') | ~m1_subset_1(B_321, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81, c_7645])).
% 9.03/3.02  tff(c_7697, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_7296, c_7683])).
% 9.03/3.02  tff(c_7706, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_7595, c_7697])).
% 9.03/3.02  tff(c_7990, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7706])).
% 9.03/3.02  tff(c_7993, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_7990])).
% 9.03/3.02  tff(c_7997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7271, c_7993])).
% 9.03/3.02  tff(c_7999, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7706])).
% 9.03/3.02  tff(c_7487, plain, (![B_306]: (k2_pre_topc('#skF_1', B_306)=k2_struct_0('#skF_1') | ~v1_tops_1(B_306, '#skF_1') | ~m1_subset_1(B_306, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7478])).
% 9.03/3.02  tff(c_8015, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_7999, c_7487])).
% 9.03/3.02  tff(c_8021, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_8015])).
% 9.03/3.02  tff(c_8024, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7654, c_8021])).
% 9.03/3.02  tff(c_8028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7271, c_7270, c_8024])).
% 9.03/3.02  tff(c_8029, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_8015])).
% 9.03/3.02  tff(c_7766, plain, (![A_326, B_327]: (k3_subset_1(u1_struct_0(A_326), k2_pre_topc(A_326, k3_subset_1(u1_struct_0(A_326), B_327)))=k1_tops_1(A_326, B_327) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_326))) | ~l1_pre_topc(A_326))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.03/3.02  tff(c_7807, plain, (![B_327]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_327)))=k1_tops_1('#skF_1', B_327) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_7766])).
% 9.03/3.02  tff(c_7819, plain, (![B_327]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_327)))=k1_tops_1('#skF_1', B_327) | ~m1_subset_1(B_327, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81, c_81, c_7807])).
% 9.03/3.02  tff(c_8042, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8029, c_7819])).
% 9.03/3.02  tff(c_8056, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7271, c_7298, c_8042])).
% 9.03/3.02  tff(c_8058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7269, c_8056])).
% 9.03/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.03/3.02  
% 9.03/3.02  Inference rules
% 9.03/3.02  ----------------------
% 9.03/3.02  #Ref     : 0
% 9.03/3.02  #Sup     : 1877
% 9.03/3.02  #Fact    : 0
% 9.03/3.02  #Define  : 0
% 9.03/3.02  #Split   : 44
% 9.03/3.02  #Chain   : 0
% 9.03/3.02  #Close   : 0
% 9.03/3.02  
% 9.03/3.02  Ordering : KBO
% 9.03/3.02  
% 9.03/3.02  Simplification rules
% 9.03/3.02  ----------------------
% 9.03/3.02  #Subsume      : 444
% 9.03/3.02  #Demod        : 1489
% 9.03/3.02  #Tautology    : 340
% 9.03/3.02  #SimpNegUnit  : 278
% 9.03/3.02  #BackRed      : 2
% 9.03/3.02  
% 9.03/3.02  #Partial instantiations: 0
% 9.03/3.02  #Strategies tried      : 1
% 9.03/3.02  
% 9.03/3.02  Timing (in seconds)
% 9.03/3.02  ----------------------
% 9.03/3.03  Preprocessing        : 0.30
% 9.03/3.03  Parsing              : 0.16
% 9.03/3.03  CNF conversion       : 0.02
% 9.03/3.03  Main loop            : 1.88
% 9.03/3.03  Inferencing          : 0.61
% 9.03/3.03  Reduction            : 0.67
% 9.03/3.03  Demodulation         : 0.44
% 9.03/3.03  BG Simplification    : 0.06
% 9.03/3.03  Subsumption          : 0.39
% 9.03/3.03  Abstraction          : 0.08
% 9.03/3.03  MUC search           : 0.00
% 9.03/3.03  Cooper               : 0.00
% 9.03/3.03  Total                : 2.22
% 9.03/3.03  Index Insertion      : 0.00
% 9.03/3.03  Index Deletion       : 0.00
% 9.03/3.03  Index Matching       : 0.00
% 9.03/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
