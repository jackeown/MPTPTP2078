%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:46 EST 2020

% Result     : Theorem 10.29s
% Output     : CNFRefutation 10.34s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 298 expanded)
%              Number of leaves         :   35 ( 113 expanded)
%              Depth                    :   14
%              Number of atoms          :  329 ( 971 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_68,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20164,plain,(
    ! [A_1244,B_1245] :
      ( v3_pre_topc(k1_tops_1(A_1244,B_1245),A_1244)
      | ~ m1_subset_1(B_1245,k1_zfmisc_1(u1_struct_0(A_1244)))
      | ~ l1_pre_topc(A_1244)
      | ~ v2_pre_topc(A_1244) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20169,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_20164])).

tff(c_20173,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_20169])).

tff(c_20081,plain,(
    ! [A_1239,B_1240] :
      ( r1_tarski(k1_tops_1(A_1239,B_1240),B_1240)
      | ~ m1_subset_1(B_1240,k1_zfmisc_1(u1_struct_0(A_1239)))
      | ~ l1_pre_topc(A_1239) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20086,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_20081])).

tff(c_20090,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20086])).

tff(c_17948,plain,(
    ! [A_1055,B_1056] :
      ( v3_pre_topc(k1_tops_1(A_1055,B_1056),A_1055)
      | ~ m1_subset_1(B_1056,k1_zfmisc_1(u1_struct_0(A_1055)))
      | ~ l1_pre_topc(A_1055)
      | ~ v2_pre_topc(A_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_17955,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_17948])).

tff(c_17960,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_17955])).

tff(c_17494,plain,(
    ! [A_1023,B_1024] :
      ( r1_tarski(k1_tops_1(A_1023,B_1024),B_1024)
      | ~ m1_subset_1(B_1024,k1_zfmisc_1(u1_struct_0(A_1023)))
      | ~ l1_pre_topc(A_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_17499,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_17494])).

tff(c_17503,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_17499])).

tff(c_14120,plain,(
    ! [A_794,B_795] :
      ( v3_pre_topc(k1_tops_1(A_794,B_795),A_794)
      | ~ m1_subset_1(B_795,k1_zfmisc_1(u1_struct_0(A_794)))
      | ~ l1_pre_topc(A_794)
      | ~ v2_pre_topc(A_794) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14127,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_14120])).

tff(c_14132,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_14127])).

tff(c_13511,plain,(
    ! [A_754,B_755] :
      ( r1_tarski(k1_tops_1(A_754,B_755),B_755)
      | ~ m1_subset_1(B_755,k1_zfmisc_1(u1_struct_0(A_754)))
      | ~ l1_pre_topc(A_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_13516,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_13511])).

tff(c_13520,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_13516])).

tff(c_12146,plain,(
    ! [A_652,B_653] :
      ( v3_pre_topc(k1_tops_1(A_652,B_653),A_652)
      | ~ m1_subset_1(B_653,k1_zfmisc_1(u1_struct_0(A_652)))
      | ~ l1_pre_topc(A_652)
      | ~ v2_pre_topc(A_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12153,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_12146])).

tff(c_12158,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_12153])).

tff(c_11579,plain,(
    ! [A_620,B_621] :
      ( r1_tarski(k1_tops_1(A_620,B_621),B_621)
      | ~ m1_subset_1(B_621,k1_zfmisc_1(u1_struct_0(A_620)))
      | ~ l1_pre_topc(A_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_11584,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_11579])).

tff(c_11588,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_11584])).

tff(c_60,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_91,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_161,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_72,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_64,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_169,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_402,plain,(
    ! [A_88,B_89] :
      ( k3_subset_1(A_88,k3_subset_1(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_407,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_169,c_402])).

tff(c_34,plain,(
    ! [A_25,B_27] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_25),B_27),A_25)
      | ~ v3_pre_topc(B_27,A_25)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k3_subset_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_930,plain,(
    ! [A_134,B_135] :
      ( k2_pre_topc(A_134,B_135) = B_135
      | ~ v4_pre_topc(B_135,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5407,plain,(
    ! [A_345,B_346] :
      ( k2_pre_topc(A_345,k3_subset_1(u1_struct_0(A_345),B_346)) = k3_subset_1(u1_struct_0(A_345),B_346)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_345),B_346),A_345)
      | ~ l1_pre_topc(A_345)
      | ~ m1_subset_1(B_346,k1_zfmisc_1(u1_struct_0(A_345))) ) ),
    inference(resolution,[status(thm)],[c_18,c_930])).

tff(c_8290,plain,(
    ! [A_426,B_427] :
      ( k2_pre_topc(A_426,k3_subset_1(u1_struct_0(A_426),B_427)) = k3_subset_1(u1_struct_0(A_426),B_427)
      | ~ v3_pre_topc(B_427,A_426)
      | ~ m1_subset_1(B_427,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_pre_topc(A_426) ) ),
    inference(resolution,[status(thm)],[c_34,c_5407])).

tff(c_8301,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_169,c_8290])).

tff(c_8316,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_91,c_8301])).

tff(c_26,plain,(
    ! [A_18,B_20] :
      ( k3_subset_1(u1_struct_0(A_18),k2_pre_topc(A_18,k3_subset_1(u1_struct_0(A_18),B_20))) = k1_tops_1(A_18,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8332,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8316,c_26])).

tff(c_8343,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_169,c_407,c_8332])).

tff(c_797,plain,(
    ! [A_130,B_131] :
      ( r1_tarski(k1_tops_1(A_130,B_131),B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_802,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_169,c_797])).

tff(c_808,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_802])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_824,plain,
    ( k1_tops_1('#skF_1','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_808,c_2])).

tff(c_1038,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_824])).

tff(c_8390,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8343,c_1038])).

tff(c_8410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8390])).

tff(c_8411,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_824])).

tff(c_9880,plain,(
    ! [A_503,B_504,C_505] :
      ( r1_tarski(k1_tops_1(A_503,B_504),k1_tops_1(A_503,C_505))
      | ~ r1_tarski(B_504,C_505)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ m1_subset_1(B_504,k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ l1_pre_topc(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9894,plain,(
    ! [C_505] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_505))
      | ~ r1_tarski('#skF_4',C_505)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8411,c_9880])).

tff(c_10581,plain,(
    ! [C_547] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_547))
      | ~ r1_tarski('#skF_4',C_547)
      | ~ m1_subset_1(C_547,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_169,c_9894])).

tff(c_10598,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_10581])).

tff(c_10609,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10598])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10624,plain,(
    k2_xboole_0('#skF_4',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10609,c_10])).

tff(c_591,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_tarski(k2_tarski(A_108,B_109),C_110)
      | ~ r2_hidden(B_109,C_110)
      | ~ r2_hidden(A_108,C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8819,plain,(
    ! [A_446,B_447,C_448] :
      ( k2_xboole_0(k2_tarski(A_446,B_447),C_448) = C_448
      | ~ r2_hidden(B_447,C_448)
      | ~ r2_hidden(A_446,C_448) ) ),
    inference(resolution,[status(thm)],[c_591,c_10])).

tff(c_82,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(k2_xboole_0(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [A_3,B_4,B_55] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_55)) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_198,plain,(
    ! [B_70,C_71,A_72] :
      ( r2_hidden(B_70,C_71)
      | ~ r1_tarski(k2_tarski(A_72,B_70),C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_211,plain,(
    ! [B_70,A_72,B_4,B_55] : r2_hidden(B_70,k2_xboole_0(k2_xboole_0(k2_tarski(A_72,B_70),B_4),B_55)) ),
    inference(resolution,[status(thm)],[c_103,c_198])).

tff(c_8899,plain,(
    ! [B_449,C_450,B_451,A_452] :
      ( r2_hidden(B_449,k2_xboole_0(C_450,B_451))
      | ~ r2_hidden(B_449,C_450)
      | ~ r2_hidden(A_452,C_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8819,c_211])).

tff(c_8926,plain,(
    ! [B_449,B_451] :
      ( r2_hidden(B_449,k2_xboole_0('#skF_4',B_451))
      | ~ r2_hidden(B_449,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_8899])).

tff(c_10795,plain,(
    ! [B_552] :
      ( r2_hidden(B_552,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(B_552,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10624,c_8926])).

tff(c_46,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_854,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_10800,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_10795,c_854])).

tff(c_10805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10800])).

tff(c_10945,plain,(
    ! [D_558] :
      ( ~ r2_hidden('#skF_2',D_558)
      | ~ r1_tarski(D_558,'#skF_3')
      | ~ v3_pre_topc(D_558,'#skF_1')
      | ~ m1_subset_1(D_558,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_10952,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_169,c_10945])).

tff(c_10960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_161,c_72,c_10952])).

tff(c_10961,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_11894,plain,(
    ! [A_635,B_636] :
      ( m1_subset_1(k1_tops_1(A_635,B_636),k1_zfmisc_1(u1_struct_0(A_635)))
      | ~ m1_subset_1(B_636,k1_zfmisc_1(u1_struct_0(A_635)))
      | ~ l1_pre_topc(A_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11643,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10961,c_46])).

tff(c_11901,plain,(
    ! [B_636] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_636))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_636),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_636),'#skF_1')
      | ~ m1_subset_1(B_636,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_11894,c_11643])).

tff(c_13283,plain,(
    ! [B_722] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_722))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_722),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_722),'#skF_1')
      | ~ m1_subset_1(B_722,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_11901])).

tff(c_13294,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_13283])).

tff(c_13302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12158,c_11588,c_10961,c_13294])).

tff(c_13303,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_13803,plain,(
    ! [A_769,B_770] :
      ( m1_subset_1(k1_tops_1(A_769,B_770),k1_zfmisc_1(u1_struct_0(A_769)))
      | ~ m1_subset_1(B_770,k1_zfmisc_1(u1_struct_0(A_769)))
      | ~ l1_pre_topc(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_13304,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_13571,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13304,c_54])).

tff(c_13810,plain,(
    ! [B_770] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_770))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_770),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_770),'#skF_1')
      | ~ m1_subset_1(B_770,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13803,c_13571])).

tff(c_17176,plain,(
    ! [B_975] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_975))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_975),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_975),'#skF_1')
      | ~ m1_subset_1(B_975,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_13810])).

tff(c_17190,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_17176])).

tff(c_17201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14132,c_13520,c_13303,c_17190])).

tff(c_17202,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_17591,plain,(
    ! [A_1029,B_1030] :
      ( m1_subset_1(k1_tops_1(A_1029,B_1030),k1_zfmisc_1(u1_struct_0(A_1029)))
      | ~ m1_subset_1(B_1030,k1_zfmisc_1(u1_struct_0(A_1029)))
      | ~ l1_pre_topc(A_1029) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17203,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_17405,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_17203,c_58])).

tff(c_17597,plain,(
    ! [B_1030] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_1030))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_1030),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_1030),'#skF_1')
      | ~ m1_subset_1(B_1030,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_17591,c_17405])).

tff(c_19764,plain,(
    ! [B_1188] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_1188))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_1188),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_1188),'#skF_1')
      | ~ m1_subset_1(B_1188,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_17597])).

tff(c_19775,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_19764])).

tff(c_19783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17960,c_17503,c_17202,c_19775])).

tff(c_19784,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_20600,plain,(
    ! [A_1276,B_1277] :
      ( m1_subset_1(k1_tops_1(A_1276,B_1277),k1_zfmisc_1(u1_struct_0(A_1276)))
      | ~ m1_subset_1(B_1277,k1_zfmisc_1(u1_struct_0(A_1276)))
      | ~ l1_pre_topc(A_1276) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_19785,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20141,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_19785,c_50])).

tff(c_20609,plain,(
    ! [B_1277] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_1277))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_1277),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_1277),'#skF_1')
      | ~ m1_subset_1(B_1277,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20600,c_20141])).

tff(c_22033,plain,(
    ! [B_1379] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_1379))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_1379),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_1379),'#skF_1')
      | ~ m1_subset_1(B_1379,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20609])).

tff(c_22044,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_22033])).

tff(c_22052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20173,c_20090,c_19784,c_22044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.29/3.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.34/3.88  
% 10.34/3.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.34/3.88  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.34/3.88  
% 10.34/3.88  %Foreground sorts:
% 10.34/3.88  
% 10.34/3.88  
% 10.34/3.88  %Background operators:
% 10.34/3.88  
% 10.34/3.88  
% 10.34/3.88  %Foreground operators:
% 10.34/3.88  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.34/3.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.34/3.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.34/3.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.34/3.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.34/3.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.34/3.88  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.34/3.88  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.34/3.88  tff('#skF_2', type, '#skF_2': $i).
% 10.34/3.88  tff('#skF_3', type, '#skF_3': $i).
% 10.34/3.88  tff('#skF_1', type, '#skF_1': $i).
% 10.34/3.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.34/3.88  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.34/3.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.34/3.88  tff('#skF_4', type, '#skF_4': $i).
% 10.34/3.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.34/3.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.34/3.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.34/3.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.34/3.88  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.34/3.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.34/3.88  
% 10.34/3.91  tff(f_136, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 10.34/3.91  tff(f_89, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 10.34/3.91  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 10.34/3.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.34/3.91  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.34/3.91  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 10.34/3.91  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.34/3.91  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 10.34/3.91  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 10.34/3.91  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 10.34/3.91  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.34/3.91  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.34/3.91  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 10.34/3.91  tff(f_81, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 10.34/3.91  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_20164, plain, (![A_1244, B_1245]: (v3_pre_topc(k1_tops_1(A_1244, B_1245), A_1244) | ~m1_subset_1(B_1245, k1_zfmisc_1(u1_struct_0(A_1244))) | ~l1_pre_topc(A_1244) | ~v2_pre_topc(A_1244))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.34/3.91  tff(c_20169, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_20164])).
% 10.34/3.91  tff(c_20173, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_20169])).
% 10.34/3.91  tff(c_20081, plain, (![A_1239, B_1240]: (r1_tarski(k1_tops_1(A_1239, B_1240), B_1240) | ~m1_subset_1(B_1240, k1_zfmisc_1(u1_struct_0(A_1239))) | ~l1_pre_topc(A_1239))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.34/3.91  tff(c_20086, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_20081])).
% 10.34/3.91  tff(c_20090, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20086])).
% 10.34/3.91  tff(c_17948, plain, (![A_1055, B_1056]: (v3_pre_topc(k1_tops_1(A_1055, B_1056), A_1055) | ~m1_subset_1(B_1056, k1_zfmisc_1(u1_struct_0(A_1055))) | ~l1_pre_topc(A_1055) | ~v2_pre_topc(A_1055))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.34/3.91  tff(c_17955, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_17948])).
% 10.34/3.91  tff(c_17960, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_17955])).
% 10.34/3.91  tff(c_17494, plain, (![A_1023, B_1024]: (r1_tarski(k1_tops_1(A_1023, B_1024), B_1024) | ~m1_subset_1(B_1024, k1_zfmisc_1(u1_struct_0(A_1023))) | ~l1_pre_topc(A_1023))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.34/3.91  tff(c_17499, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_17494])).
% 10.34/3.91  tff(c_17503, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_17499])).
% 10.34/3.91  tff(c_14120, plain, (![A_794, B_795]: (v3_pre_topc(k1_tops_1(A_794, B_795), A_794) | ~m1_subset_1(B_795, k1_zfmisc_1(u1_struct_0(A_794))) | ~l1_pre_topc(A_794) | ~v2_pre_topc(A_794))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.34/3.91  tff(c_14127, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_14120])).
% 10.34/3.91  tff(c_14132, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_14127])).
% 10.34/3.91  tff(c_13511, plain, (![A_754, B_755]: (r1_tarski(k1_tops_1(A_754, B_755), B_755) | ~m1_subset_1(B_755, k1_zfmisc_1(u1_struct_0(A_754))) | ~l1_pre_topc(A_754))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.34/3.91  tff(c_13516, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_13511])).
% 10.34/3.91  tff(c_13520, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_13516])).
% 10.34/3.91  tff(c_12146, plain, (![A_652, B_653]: (v3_pre_topc(k1_tops_1(A_652, B_653), A_652) | ~m1_subset_1(B_653, k1_zfmisc_1(u1_struct_0(A_652))) | ~l1_pre_topc(A_652) | ~v2_pre_topc(A_652))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.34/3.91  tff(c_12153, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_12146])).
% 10.34/3.91  tff(c_12158, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_12153])).
% 10.34/3.91  tff(c_11579, plain, (![A_620, B_621]: (r1_tarski(k1_tops_1(A_620, B_621), B_621) | ~m1_subset_1(B_621, k1_zfmisc_1(u1_struct_0(A_620))) | ~l1_pre_topc(A_620))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.34/3.91  tff(c_11584, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_11579])).
% 10.34/3.91  tff(c_11588, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_11584])).
% 10.34/3.91  tff(c_60, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_91, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_60])).
% 10.34/3.91  tff(c_56, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_161, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 10.34/3.91  tff(c_52, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_72, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 10.34/3.91  tff(c_64, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_64])).
% 10.34/3.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.34/3.91  tff(c_402, plain, (![A_88, B_89]: (k3_subset_1(A_88, k3_subset_1(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.34/3.91  tff(c_407, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_169, c_402])).
% 10.34/3.91  tff(c_34, plain, (![A_25, B_27]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_25), B_27), A_25) | ~v3_pre_topc(B_27, A_25) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.34/3.91  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(k3_subset_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.34/3.91  tff(c_930, plain, (![A_134, B_135]: (k2_pre_topc(A_134, B_135)=B_135 | ~v4_pre_topc(B_135, A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.34/3.91  tff(c_5407, plain, (![A_345, B_346]: (k2_pre_topc(A_345, k3_subset_1(u1_struct_0(A_345), B_346))=k3_subset_1(u1_struct_0(A_345), B_346) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_345), B_346), A_345) | ~l1_pre_topc(A_345) | ~m1_subset_1(B_346, k1_zfmisc_1(u1_struct_0(A_345))))), inference(resolution, [status(thm)], [c_18, c_930])).
% 10.34/3.91  tff(c_8290, plain, (![A_426, B_427]: (k2_pre_topc(A_426, k3_subset_1(u1_struct_0(A_426), B_427))=k3_subset_1(u1_struct_0(A_426), B_427) | ~v3_pre_topc(B_427, A_426) | ~m1_subset_1(B_427, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_pre_topc(A_426))), inference(resolution, [status(thm)], [c_34, c_5407])).
% 10.34/3.91  tff(c_8301, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_169, c_8290])).
% 10.34/3.91  tff(c_8316, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_91, c_8301])).
% 10.34/3.91  tff(c_26, plain, (![A_18, B_20]: (k3_subset_1(u1_struct_0(A_18), k2_pre_topc(A_18, k3_subset_1(u1_struct_0(A_18), B_20)))=k1_tops_1(A_18, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.34/3.91  tff(c_8332, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8316, c_26])).
% 10.34/3.91  tff(c_8343, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_169, c_407, c_8332])).
% 10.34/3.91  tff(c_797, plain, (![A_130, B_131]: (r1_tarski(k1_tops_1(A_130, B_131), B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.34/3.91  tff(c_802, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_169, c_797])).
% 10.34/3.91  tff(c_808, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_802])).
% 10.34/3.91  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.34/3.91  tff(c_824, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_808, c_2])).
% 10.34/3.91  tff(c_1038, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_824])).
% 10.34/3.91  tff(c_8390, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8343, c_1038])).
% 10.34/3.91  tff(c_8410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8390])).
% 10.34/3.91  tff(c_8411, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_824])).
% 10.34/3.91  tff(c_9880, plain, (![A_503, B_504, C_505]: (r1_tarski(k1_tops_1(A_503, B_504), k1_tops_1(A_503, C_505)) | ~r1_tarski(B_504, C_505) | ~m1_subset_1(C_505, k1_zfmisc_1(u1_struct_0(A_503))) | ~m1_subset_1(B_504, k1_zfmisc_1(u1_struct_0(A_503))) | ~l1_pre_topc(A_503))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.34/3.91  tff(c_9894, plain, (![C_505]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_505)) | ~r1_tarski('#skF_4', C_505) | ~m1_subset_1(C_505, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8411, c_9880])).
% 10.34/3.91  tff(c_10581, plain, (![C_547]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_547)) | ~r1_tarski('#skF_4', C_547) | ~m1_subset_1(C_547, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_169, c_9894])).
% 10.34/3.91  tff(c_10598, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_10581])).
% 10.34/3.91  tff(c_10609, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_10598])).
% 10.34/3.91  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.34/3.91  tff(c_10624, plain, (k2_xboole_0('#skF_4', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10609, c_10])).
% 10.34/3.91  tff(c_591, plain, (![A_108, B_109, C_110]: (r1_tarski(k2_tarski(A_108, B_109), C_110) | ~r2_hidden(B_109, C_110) | ~r2_hidden(A_108, C_110))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.34/3.91  tff(c_8819, plain, (![A_446, B_447, C_448]: (k2_xboole_0(k2_tarski(A_446, B_447), C_448)=C_448 | ~r2_hidden(B_447, C_448) | ~r2_hidden(A_446, C_448))), inference(resolution, [status(thm)], [c_591, c_10])).
% 10.34/3.91  tff(c_82, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(k2_xboole_0(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.34/3.91  tff(c_92, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(resolution, [status(thm)], [c_6, c_82])).
% 10.34/3.91  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.34/3.91  tff(c_103, plain, (![A_3, B_4, B_55]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_55)))), inference(resolution, [status(thm)], [c_92, c_8])).
% 10.34/3.91  tff(c_198, plain, (![B_70, C_71, A_72]: (r2_hidden(B_70, C_71) | ~r1_tarski(k2_tarski(A_72, B_70), C_71))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.34/3.91  tff(c_211, plain, (![B_70, A_72, B_4, B_55]: (r2_hidden(B_70, k2_xboole_0(k2_xboole_0(k2_tarski(A_72, B_70), B_4), B_55)))), inference(resolution, [status(thm)], [c_103, c_198])).
% 10.34/3.91  tff(c_8899, plain, (![B_449, C_450, B_451, A_452]: (r2_hidden(B_449, k2_xboole_0(C_450, B_451)) | ~r2_hidden(B_449, C_450) | ~r2_hidden(A_452, C_450))), inference(superposition, [status(thm), theory('equality')], [c_8819, c_211])).
% 10.34/3.91  tff(c_8926, plain, (![B_449, B_451]: (r2_hidden(B_449, k2_xboole_0('#skF_4', B_451)) | ~r2_hidden(B_449, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_8899])).
% 10.34/3.91  tff(c_10795, plain, (![B_552]: (r2_hidden(B_552, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(B_552, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10624, c_8926])).
% 10.34/3.91  tff(c_46, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_854, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_46])).
% 10.34/3.91  tff(c_10800, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_10795, c_854])).
% 10.34/3.91  tff(c_10805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_10800])).
% 10.34/3.91  tff(c_10945, plain, (![D_558]: (~r2_hidden('#skF_2', D_558) | ~r1_tarski(D_558, '#skF_3') | ~v3_pre_topc(D_558, '#skF_1') | ~m1_subset_1(D_558, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_46])).
% 10.34/3.91  tff(c_10952, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_169, c_10945])).
% 10.34/3.91  tff(c_10960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_161, c_72, c_10952])).
% 10.34/3.91  tff(c_10961, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 10.34/3.91  tff(c_11894, plain, (![A_635, B_636]: (m1_subset_1(k1_tops_1(A_635, B_636), k1_zfmisc_1(u1_struct_0(A_635))) | ~m1_subset_1(B_636, k1_zfmisc_1(u1_struct_0(A_635))) | ~l1_pre_topc(A_635))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.34/3.91  tff(c_11643, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_10961, c_46])).
% 10.34/3.91  tff(c_11901, plain, (![B_636]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_636)) | ~r1_tarski(k1_tops_1('#skF_1', B_636), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_636), '#skF_1') | ~m1_subset_1(B_636, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_11894, c_11643])).
% 10.34/3.91  tff(c_13283, plain, (![B_722]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_722)) | ~r1_tarski(k1_tops_1('#skF_1', B_722), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_722), '#skF_1') | ~m1_subset_1(B_722, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_11901])).
% 10.34/3.91  tff(c_13294, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_40, c_13283])).
% 10.34/3.91  tff(c_13302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12158, c_11588, c_10961, c_13294])).
% 10.34/3.91  tff(c_13303, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 10.34/3.91  tff(c_13803, plain, (![A_769, B_770]: (m1_subset_1(k1_tops_1(A_769, B_770), k1_zfmisc_1(u1_struct_0(A_769))) | ~m1_subset_1(B_770, k1_zfmisc_1(u1_struct_0(A_769))) | ~l1_pre_topc(A_769))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.34/3.91  tff(c_13304, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 10.34/3.91  tff(c_54, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_13571, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_13304, c_54])).
% 10.34/3.91  tff(c_13810, plain, (![B_770]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_770)) | ~r1_tarski(k1_tops_1('#skF_1', B_770), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_770), '#skF_1') | ~m1_subset_1(B_770, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_13803, c_13571])).
% 10.34/3.91  tff(c_17176, plain, (![B_975]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_975)) | ~r1_tarski(k1_tops_1('#skF_1', B_975), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_975), '#skF_1') | ~m1_subset_1(B_975, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_13810])).
% 10.34/3.91  tff(c_17190, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_40, c_17176])).
% 10.34/3.91  tff(c_17201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14132, c_13520, c_13303, c_17190])).
% 10.34/3.91  tff(c_17202, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 10.34/3.91  tff(c_17591, plain, (![A_1029, B_1030]: (m1_subset_1(k1_tops_1(A_1029, B_1030), k1_zfmisc_1(u1_struct_0(A_1029))) | ~m1_subset_1(B_1030, k1_zfmisc_1(u1_struct_0(A_1029))) | ~l1_pre_topc(A_1029))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.34/3.91  tff(c_17203, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_60])).
% 10.34/3.91  tff(c_58, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_17405, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_17203, c_58])).
% 10.34/3.91  tff(c_17597, plain, (![B_1030]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_1030)) | ~r1_tarski(k1_tops_1('#skF_1', B_1030), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_1030), '#skF_1') | ~m1_subset_1(B_1030, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_17591, c_17405])).
% 10.34/3.91  tff(c_19764, plain, (![B_1188]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_1188)) | ~r1_tarski(k1_tops_1('#skF_1', B_1188), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_1188), '#skF_1') | ~m1_subset_1(B_1188, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_17597])).
% 10.34/3.91  tff(c_19775, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_40, c_19764])).
% 10.34/3.91  tff(c_19783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17960, c_17503, c_17202, c_19775])).
% 10.34/3.91  tff(c_19784, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 10.34/3.91  tff(c_20600, plain, (![A_1276, B_1277]: (m1_subset_1(k1_tops_1(A_1276, B_1277), k1_zfmisc_1(u1_struct_0(A_1276))) | ~m1_subset_1(B_1277, k1_zfmisc_1(u1_struct_0(A_1276))) | ~l1_pre_topc(A_1276))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.34/3.91  tff(c_19785, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 10.34/3.91  tff(c_50, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.34/3.91  tff(c_20141, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_19785, c_50])).
% 10.34/3.91  tff(c_20609, plain, (![B_1277]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_1277)) | ~r1_tarski(k1_tops_1('#skF_1', B_1277), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_1277), '#skF_1') | ~m1_subset_1(B_1277, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_20600, c_20141])).
% 10.34/3.91  tff(c_22033, plain, (![B_1379]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_1379)) | ~r1_tarski(k1_tops_1('#skF_1', B_1379), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_1379), '#skF_1') | ~m1_subset_1(B_1379, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20609])).
% 10.34/3.91  tff(c_22044, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_40, c_22033])).
% 10.34/3.91  tff(c_22052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20173, c_20090, c_19784, c_22044])).
% 10.34/3.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.34/3.91  
% 10.34/3.91  Inference rules
% 10.34/3.91  ----------------------
% 10.34/3.91  #Ref     : 0
% 10.34/3.91  #Sup     : 5282
% 10.34/3.91  #Fact    : 0
% 10.34/3.91  #Define  : 0
% 10.34/3.91  #Split   : 45
% 10.34/3.91  #Chain   : 0
% 10.34/3.91  #Close   : 0
% 10.34/3.91  
% 10.34/3.91  Ordering : KBO
% 10.34/3.91  
% 10.34/3.91  Simplification rules
% 10.34/3.91  ----------------------
% 10.34/3.91  #Subsume      : 1506
% 10.34/3.91  #Demod        : 2508
% 10.34/3.91  #Tautology    : 1708
% 10.34/3.91  #SimpNegUnit  : 38
% 10.34/3.91  #BackRed      : 72
% 10.34/3.91  
% 10.34/3.91  #Partial instantiations: 0
% 10.34/3.91  #Strategies tried      : 1
% 10.34/3.91  
% 10.34/3.91  Timing (in seconds)
% 10.34/3.91  ----------------------
% 10.48/3.91  Preprocessing        : 0.34
% 10.48/3.91  Parsing              : 0.20
% 10.48/3.91  CNF conversion       : 0.03
% 10.48/3.91  Main loop            : 2.74
% 10.48/3.91  Inferencing          : 0.78
% 10.48/3.91  Reduction            : 1.09
% 10.48/3.91  Demodulation         : 0.85
% 10.48/3.91  BG Simplification    : 0.08
% 10.48/3.91  Subsumption          : 0.61
% 10.48/3.91  Abstraction          : 0.11
% 10.48/3.91  MUC search           : 0.00
% 10.48/3.91  Cooper               : 0.00
% 10.48/3.91  Total                : 3.13
% 10.48/3.91  Index Insertion      : 0.00
% 10.48/3.91  Index Deletion       : 0.00
% 10.48/3.91  Index Matching       : 0.00
% 10.48/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
