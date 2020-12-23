%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:14 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 401 expanded)
%              Number of leaves         :   33 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 (1481 expanded)
%              Number of equality atoms :   24 (  90 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_123,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_137,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_123])).

tff(c_12,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_145,plain,(
    ! [A_44] : r1_tarski(k1_xboole_0,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_12])).

tff(c_60,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_85,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_87,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_54])).

tff(c_20,plain,(
    ! [A_11] :
      ( v1_zfmisc_1(A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_434,plain,(
    ! [A_64,B_65] :
      ( '#skF_1'(A_64,B_65) != B_65
      | v3_tex_2(B_65,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_437,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_434])).

tff(c_440,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_437])).

tff(c_441,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_440])).

tff(c_442,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1108,plain,(
    ! [B_85,A_86] :
      ( v2_tex_2(B_85,A_86)
      | ~ v1_zfmisc_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | v1_xboole_0(B_85)
      | ~ l1_pre_topc(A_86)
      | ~ v2_tdlat_3(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1114,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1108])).

tff(c_1118,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_85,c_1114])).

tff(c_1120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_442,c_1118])).

tff(c_1121,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_1122,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_1333,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(B_92,'#skF_1'(A_93,B_92))
      | v3_tex_2(B_92,A_93)
      | ~ v2_tex_2(B_92,A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1335,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1333])).

tff(c_1338,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1122,c_1335])).

tff(c_1339,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1338])).

tff(c_36,plain,(
    ! [B_25,A_23] :
      ( B_25 = A_23
      | ~ r1_tarski(A_23,B_25)
      | ~ v1_zfmisc_1(B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1342,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1339,c_36])).

tff(c_1347,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1121,c_1342])).

tff(c_1351,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1347])).

tff(c_1355,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_1351])).

tff(c_1531,plain,(
    ! [A_97,B_98] :
      ( v2_tex_2('#skF_1'(A_97,B_98),A_97)
      | v3_tex_2(B_98,A_97)
      | ~ v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1533,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1531])).

tff(c_1536,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1122,c_1533])).

tff(c_1537,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1536])).

tff(c_1988,plain,(
    ! [A_110,B_111] :
      ( m1_subset_1('#skF_1'(A_110,B_111),k1_zfmisc_1(u1_struct_0(A_110)))
      | v3_tex_2(B_111,A_110)
      | ~ v2_tex_2(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [B_28,A_26] :
      ( v1_zfmisc_1(B_28)
      | ~ v2_tex_2(B_28,A_26)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | v1_xboole_0(B_28)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5633,plain,(
    ! [A_150,B_151] :
      ( v1_zfmisc_1('#skF_1'(A_150,B_151))
      | ~ v2_tex_2('#skF_1'(A_150,B_151),A_150)
      | v1_xboole_0('#skF_1'(A_150,B_151))
      | ~ v2_tdlat_3(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150)
      | v3_tex_2(B_151,A_150)
      | ~ v2_tex_2(B_151,A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_1988,c_40])).

tff(c_5637,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1537,c_5633])).

tff(c_5641,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1122,c_50,c_48,c_5637])).

tff(c_5643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_52,c_1355,c_1351,c_5641])).

tff(c_5644,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1347])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | B_36 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_2,c_88])).

tff(c_5651,plain,(
    '#skF_1'('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5644,c_91])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1344,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1339,c_4])).

tff(c_1350,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1121,c_1344])).

tff(c_5659,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5651,c_1350])).

tff(c_5665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_5659])).

tff(c_5667,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_5666,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_5668,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_5674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5666,c_5668])).

tff(c_5676,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5993,plain,(
    ! [B_176,A_177] :
      ( v2_tex_2(B_176,A_177)
      | ~ v3_tex_2(B_176,A_177)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5996,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_5993])).

tff(c_5999,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5676,c_5996])).

tff(c_6425,plain,(
    ! [B_208,A_209] :
      ( v1_zfmisc_1(B_208)
      | ~ v2_tex_2(B_208,A_209)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_209)))
      | v1_xboole_0(B_208)
      | ~ l1_pre_topc(A_209)
      | ~ v2_tdlat_3(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6431,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_6425])).

tff(c_6435,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_5999,c_6431])).

tff(c_6437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_5667,c_6435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.11  
% 5.75/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.12  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.75/2.12  
% 5.75/2.12  %Foreground sorts:
% 5.75/2.12  
% 5.75/2.12  
% 5.75/2.12  %Background operators:
% 5.75/2.12  
% 5.75/2.12  
% 5.75/2.12  %Foreground operators:
% 5.75/2.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.75/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.75/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.75/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.12  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.75/2.12  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.75/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.12  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.75/2.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.75/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.75/2.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.75/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.75/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.12  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.75/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.12  
% 5.75/2.14  tff(f_128, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 5.75/2.14  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.75/2.14  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.75/2.14  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.75/2.14  tff(f_36, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.75/2.14  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 5.75/2.14  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 5.75/2.14  tff(f_108, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 5.75/2.14  tff(f_89, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 5.75/2.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.75/2.14  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.75/2.14  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.75/2.14  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.75/2.14  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.75/2.14  tff(c_10, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.75/2.14  tff(c_14, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.14  tff(c_105, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.75/2.14  tff(c_123, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_105])).
% 5.75/2.14  tff(c_137, plain, (![A_44]: (k4_xboole_0(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_123])).
% 5.75/2.14  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.75/2.14  tff(c_145, plain, (![A_44]: (r1_tarski(k1_xboole_0, A_44))), inference(superposition, [status(thm), theory('equality')], [c_137, c_12])).
% 5.75/2.14  tff(c_60, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.75/2.14  tff(c_85, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 5.75/2.14  tff(c_54, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.75/2.14  tff(c_87, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_54])).
% 5.75/2.14  tff(c_20, plain, (![A_11]: (v1_zfmisc_1(A_11) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.75/2.14  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.75/2.14  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.75/2.14  tff(c_434, plain, (![A_64, B_65]: ('#skF_1'(A_64, B_65)!=B_65 | v3_tex_2(B_65, A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.75/2.14  tff(c_437, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_434])).
% 5.75/2.14  tff(c_440, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_437])).
% 5.75/2.14  tff(c_441, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_87, c_440])).
% 5.75/2.14  tff(c_442, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_441])).
% 5.75/2.14  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.75/2.14  tff(c_48, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.75/2.14  tff(c_1108, plain, (![B_85, A_86]: (v2_tex_2(B_85, A_86) | ~v1_zfmisc_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | v1_xboole_0(B_85) | ~l1_pre_topc(A_86) | ~v2_tdlat_3(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.14  tff(c_1114, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1108])).
% 5.75/2.14  tff(c_1118, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_85, c_1114])).
% 5.75/2.14  tff(c_1120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_442, c_1118])).
% 5.75/2.14  tff(c_1121, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_441])).
% 5.75/2.14  tff(c_1122, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_441])).
% 5.75/2.14  tff(c_1333, plain, (![B_92, A_93]: (r1_tarski(B_92, '#skF_1'(A_93, B_92)) | v3_tex_2(B_92, A_93) | ~v2_tex_2(B_92, A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.75/2.14  tff(c_1335, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1333])).
% 5.75/2.14  tff(c_1338, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1122, c_1335])).
% 5.75/2.14  tff(c_1339, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_87, c_1338])).
% 5.75/2.14  tff(c_36, plain, (![B_25, A_23]: (B_25=A_23 | ~r1_tarski(A_23, B_25) | ~v1_zfmisc_1(B_25) | v1_xboole_0(B_25) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.75/2.14  tff(c_1342, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1339, c_36])).
% 5.75/2.14  tff(c_1347, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_1121, c_1342])).
% 5.75/2.14  tff(c_1351, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1347])).
% 5.75/2.14  tff(c_1355, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_1351])).
% 5.75/2.14  tff(c_1531, plain, (![A_97, B_98]: (v2_tex_2('#skF_1'(A_97, B_98), A_97) | v3_tex_2(B_98, A_97) | ~v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.75/2.14  tff(c_1533, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1531])).
% 5.75/2.14  tff(c_1536, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1122, c_1533])).
% 5.75/2.14  tff(c_1537, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_87, c_1536])).
% 5.75/2.14  tff(c_1988, plain, (![A_110, B_111]: (m1_subset_1('#skF_1'(A_110, B_111), k1_zfmisc_1(u1_struct_0(A_110))) | v3_tex_2(B_111, A_110) | ~v2_tex_2(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.75/2.14  tff(c_40, plain, (![B_28, A_26]: (v1_zfmisc_1(B_28) | ~v2_tex_2(B_28, A_26) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | v1_xboole_0(B_28) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.14  tff(c_5633, plain, (![A_150, B_151]: (v1_zfmisc_1('#skF_1'(A_150, B_151)) | ~v2_tex_2('#skF_1'(A_150, B_151), A_150) | v1_xboole_0('#skF_1'(A_150, B_151)) | ~v2_tdlat_3(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150) | v3_tex_2(B_151, A_150) | ~v2_tex_2(B_151, A_150) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_1988, c_40])).
% 5.75/2.14  tff(c_5637, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1537, c_5633])).
% 5.75/2.14  tff(c_5641, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_1122, c_50, c_48, c_5637])).
% 5.75/2.14  tff(c_5643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_52, c_1355, c_1351, c_5641])).
% 5.75/2.14  tff(c_5644, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1347])).
% 5.75/2.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.75/2.14  tff(c_88, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | B_36=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.14  tff(c_91, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_2, c_88])).
% 5.75/2.14  tff(c_5651, plain, ('#skF_1'('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_5644, c_91])).
% 5.75/2.14  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.14  tff(c_1344, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1339, c_4])).
% 5.75/2.14  tff(c_1350, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1121, c_1344])).
% 5.75/2.14  tff(c_5659, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5651, c_1350])).
% 5.75/2.14  tff(c_5665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_5659])).
% 5.75/2.14  tff(c_5667, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 5.75/2.14  tff(c_5666, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 5.75/2.14  tff(c_5668, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 5.75/2.14  tff(c_5674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5666, c_5668])).
% 5.75/2.14  tff(c_5676, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 5.75/2.14  tff(c_5993, plain, (![B_176, A_177]: (v2_tex_2(B_176, A_177) | ~v3_tex_2(B_176, A_177) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.75/2.14  tff(c_5996, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_5993])).
% 5.75/2.14  tff(c_5999, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5676, c_5996])).
% 5.75/2.14  tff(c_6425, plain, (![B_208, A_209]: (v1_zfmisc_1(B_208) | ~v2_tex_2(B_208, A_209) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_209))) | v1_xboole_0(B_208) | ~l1_pre_topc(A_209) | ~v2_tdlat_3(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.14  tff(c_6431, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_6425])).
% 5.75/2.14  tff(c_6435, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_5999, c_6431])).
% 5.75/2.14  tff(c_6437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_5667, c_6435])).
% 5.75/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.14  
% 5.75/2.14  Inference rules
% 5.75/2.14  ----------------------
% 5.75/2.14  #Ref     : 0
% 5.75/2.14  #Sup     : 1417
% 5.75/2.14  #Fact    : 4
% 5.75/2.14  #Define  : 0
% 5.75/2.14  #Split   : 10
% 5.75/2.14  #Chain   : 0
% 5.75/2.14  #Close   : 0
% 5.75/2.14  
% 5.75/2.14  Ordering : KBO
% 5.75/2.14  
% 5.75/2.14  Simplification rules
% 5.75/2.14  ----------------------
% 5.75/2.14  #Subsume      : 479
% 5.75/2.14  #Demod        : 2313
% 5.75/2.14  #Tautology    : 728
% 5.75/2.14  #SimpNegUnit  : 411
% 5.75/2.14  #BackRed      : 5
% 5.75/2.14  
% 5.75/2.14  #Partial instantiations: 0
% 5.75/2.14  #Strategies tried      : 1
% 5.75/2.14  
% 5.75/2.14  Timing (in seconds)
% 5.75/2.14  ----------------------
% 5.75/2.14  Preprocessing        : 0.32
% 5.75/2.14  Parsing              : 0.17
% 5.75/2.14  CNF conversion       : 0.02
% 5.75/2.14  Main loop            : 1.04
% 5.75/2.14  Inferencing          : 0.32
% 5.75/2.14  Reduction            : 0.42
% 5.75/2.14  Demodulation         : 0.32
% 5.75/2.14  BG Simplification    : 0.04
% 5.75/2.14  Subsumption          : 0.20
% 5.75/2.14  Abstraction          : 0.05
% 5.75/2.14  MUC search           : 0.00
% 5.75/2.14  Cooper               : 0.00
% 5.75/2.14  Total                : 1.40
% 5.75/2.14  Index Insertion      : 0.00
% 5.75/2.14  Index Deletion       : 0.00
% 5.75/2.14  Index Matching       : 0.00
% 5.75/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
