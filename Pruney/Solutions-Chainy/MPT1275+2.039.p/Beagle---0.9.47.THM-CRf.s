%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:07 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 276 expanded)
%              Number of leaves         :   41 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 592 expanded)
%              Number of equality atoms :   38 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_78,axiom,(
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

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(c_54,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_82,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( k2_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_88,plain,(
    ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_48])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_22,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_67,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_76,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_77,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_476,plain,(
    ! [B_104,A_105] :
      ( v2_tops_1(B_104,A_105)
      | ~ r1_tarski(B_104,k2_tops_1(A_105,B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_480,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_476])).

tff(c_485,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_77,c_76,c_96,c_480])).

tff(c_42,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_573,plain,(
    ! [B_124,A_125] :
      ( v3_tops_1(B_124,A_125)
      | ~ v4_pre_topc(B_124,A_125)
      | ~ v2_tops_1(B_124,A_125)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_580,plain,(
    ! [B_124] :
      ( v3_tops_1(B_124,'#skF_2')
      | ~ v4_pre_topc(B_124,'#skF_2')
      | ~ v2_tops_1(B_124,'#skF_2')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_573])).

tff(c_599,plain,(
    ! [B_127] :
      ( v3_tops_1(B_127,'#skF_2')
      | ~ v4_pre_topc(B_127,'#skF_2')
      | ~ v2_tops_1(B_127,'#skF_2')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_580])).

tff(c_606,plain,
    ( v3_tops_1('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_599])).

tff(c_614,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_42,c_606])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_614])).

tff(c_617,plain,(
    v3_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_620,plain,(
    k2_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_48])).

tff(c_647,plain,(
    ! [C_139,A_140,B_141] :
      ( r2_hidden(C_139,A_140)
      | ~ r2_hidden(C_139,B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_692,plain,(
    ! [A_153,B_154,A_155] :
      ( r2_hidden('#skF_1'(A_153,B_154),A_155)
      | ~ m1_subset_1(A_153,k1_zfmisc_1(A_155))
      | r1_tarski(A_153,B_154) ) ),
    inference(resolution,[status(thm)],[c_6,c_647])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_720,plain,(
    ! [A_158,A_159] :
      ( ~ m1_subset_1(A_158,k1_zfmisc_1(A_159))
      | r1_tarski(A_158,A_159) ) ),
    inference(resolution,[status(thm)],[c_692,c_4])).

tff(c_731,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_77,c_720])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_737,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_731,c_8])).

tff(c_704,plain,(
    ! [A_156,B_157] :
      ( k2_pre_topc(A_156,B_157) = B_157
      | ~ v4_pre_topc(B_157,A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_711,plain,(
    ! [B_157] :
      ( k2_pre_topc('#skF_2',B_157) = B_157
      | ~ v4_pre_topc(B_157,'#skF_2')
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_704])).

tff(c_742,plain,(
    ! [B_160] :
      ( k2_pre_topc('#skF_2',B_160) = B_160
      | ~ v4_pre_topc(B_160,'#skF_2')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_711])).

tff(c_749,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_742])).

tff(c_757,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_749])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_652,plain,(
    ! [A_144,B_145,C_146] :
      ( k9_subset_1(A_144,B_145,C_146) = k3_xboole_0(B_145,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_661,plain,(
    ! [A_9,B_145] : k9_subset_1(A_9,B_145,A_9) = k3_xboole_0(B_145,A_9) ),
    inference(resolution,[status(thm)],[c_55,c_652])).

tff(c_1034,plain,(
    ! [A_194,B_195] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_194),B_195),A_194)
      | ~ v3_tops_1(B_195,A_194)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1037,plain,(
    ! [B_195] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_195),'#skF_2')
      | ~ v3_tops_1(B_195,'#skF_2')
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1034])).

tff(c_1039,plain,(
    ! [B_195] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_195),'#skF_2')
      | ~ v3_tops_1(B_195,'#skF_2')
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_76,c_1037])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_775,plain,(
    ! [A_164,B_165] :
      ( k2_pre_topc(A_164,B_165) = k2_struct_0(A_164)
      | ~ v1_tops_1(B_165,A_164)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1362,plain,(
    ! [A_244,B_245] :
      ( k2_pre_topc(A_244,k3_subset_1(u1_struct_0(A_244),B_245)) = k2_struct_0(A_244)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_244),B_245),A_244)
      | ~ l1_pre_topc(A_244)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244))) ) ),
    inference(resolution,[status(thm)],[c_14,c_775])).

tff(c_1368,plain,(
    ! [B_245] :
      ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_245)) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_245),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1362])).

tff(c_1392,plain,(
    ! [B_249] :
      ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_249)) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_249),'#skF_2')
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_76,c_1368])).

tff(c_1397,plain,(
    ! [B_250] :
      ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_250)) = k2_struct_0('#skF_2')
      | ~ v3_tops_1(B_250,'#skF_2')
      | ~ m1_subset_1(B_250,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1039,c_1392])).

tff(c_1404,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v3_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_1397])).

tff(c_1412,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_1404])).

tff(c_1234,plain,(
    ! [A_225,B_226] :
      ( k9_subset_1(u1_struct_0(A_225),k2_pre_topc(A_225,B_226),k2_pre_topc(A_225,k3_subset_1(u1_struct_0(A_225),B_226))) = k2_tops_1(A_225,B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1246,plain,(
    ! [B_226] :
      ( k9_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',B_226),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_226))) = k2_tops_1('#skF_2',B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1234])).

tff(c_1255,plain,(
    ! [B_226] :
      ( k9_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',B_226),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_226))) = k2_tops_1('#skF_2',B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_76,c_76,c_1246])).

tff(c_1421,plain,
    ( k9_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),k2_struct_0('#skF_2')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1412,c_1255])).

tff(c_1428,plain,(
    k2_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_737,c_757,c_661,c_1421])).

tff(c_1430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_1428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.66  
% 3.66/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.66  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.66  
% 3.66/1.66  %Foreground sorts:
% 3.66/1.66  
% 3.66/1.66  
% 3.66/1.66  %Background operators:
% 3.66/1.66  
% 3.66/1.66  
% 3.66/1.66  %Foreground operators:
% 3.66/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.66  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.66/1.66  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.66/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.66/1.66  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.66/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.66/1.66  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.66/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.66/1.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.66/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.66/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.66/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.66/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.66/1.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.66/1.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.66/1.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.66/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.66  
% 3.66/1.68  tff(f_135, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 3.66/1.68  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.66/1.68  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.66/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.66/1.68  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 3.66/1.68  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 3.66/1.68  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.66/1.68  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.66/1.68  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.66/1.68  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.66/1.68  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.66/1.68  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.66/1.68  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 3.66/1.68  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.66/1.68  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.66/1.68  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 3.66/1.68  tff(c_54, plain, (v3_tops_1('#skF_3', '#skF_2') | k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.66/1.68  tff(c_82, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_54])).
% 3.66/1.68  tff(c_48, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~v3_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.66/1.68  tff(c_88, plain, (~v3_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_48])).
% 3.66/1.68  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.66/1.68  tff(c_22, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.66/1.68  tff(c_67, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.66/1.68  tff(c_72, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_22, c_67])).
% 3.66/1.68  tff(c_76, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_72])).
% 3.66/1.68  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.66/1.68  tff(c_77, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_44])).
% 3.66/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.68  tff(c_91, plain, (![A_49, B_50]: (~r2_hidden('#skF_1'(A_49, B_50), B_50) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.68  tff(c_96, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_91])).
% 3.66/1.68  tff(c_476, plain, (![B_104, A_105]: (v2_tops_1(B_104, A_105) | ~r1_tarski(B_104, k2_tops_1(A_105, B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.66/1.68  tff(c_480, plain, (v2_tops_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_82, c_476])).
% 3.66/1.68  tff(c_485, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_77, c_76, c_96, c_480])).
% 3.66/1.68  tff(c_42, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.66/1.68  tff(c_573, plain, (![B_124, A_125]: (v3_tops_1(B_124, A_125) | ~v4_pre_topc(B_124, A_125) | ~v2_tops_1(B_124, A_125) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.66/1.68  tff(c_580, plain, (![B_124]: (v3_tops_1(B_124, '#skF_2') | ~v4_pre_topc(B_124, '#skF_2') | ~v2_tops_1(B_124, '#skF_2') | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_573])).
% 3.66/1.68  tff(c_599, plain, (![B_127]: (v3_tops_1(B_127, '#skF_2') | ~v4_pre_topc(B_127, '#skF_2') | ~v2_tops_1(B_127, '#skF_2') | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_580])).
% 3.66/1.68  tff(c_606, plain, (v3_tops_1('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_77, c_599])).
% 3.66/1.68  tff(c_614, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_42, c_606])).
% 3.66/1.68  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_614])).
% 3.66/1.68  tff(c_617, plain, (v3_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 3.66/1.68  tff(c_620, plain, (k2_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_617, c_48])).
% 3.66/1.68  tff(c_647, plain, (![C_139, A_140, B_141]: (r2_hidden(C_139, A_140) | ~r2_hidden(C_139, B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(A_140)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.66/1.68  tff(c_692, plain, (![A_153, B_154, A_155]: (r2_hidden('#skF_1'(A_153, B_154), A_155) | ~m1_subset_1(A_153, k1_zfmisc_1(A_155)) | r1_tarski(A_153, B_154))), inference(resolution, [status(thm)], [c_6, c_647])).
% 3.66/1.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.68  tff(c_720, plain, (![A_158, A_159]: (~m1_subset_1(A_158, k1_zfmisc_1(A_159)) | r1_tarski(A_158, A_159))), inference(resolution, [status(thm)], [c_692, c_4])).
% 3.66/1.68  tff(c_731, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_77, c_720])).
% 3.66/1.68  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.66/1.68  tff(c_737, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_731, c_8])).
% 3.66/1.68  tff(c_704, plain, (![A_156, B_157]: (k2_pre_topc(A_156, B_157)=B_157 | ~v4_pre_topc(B_157, A_156) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.66/1.68  tff(c_711, plain, (![B_157]: (k2_pre_topc('#skF_2', B_157)=B_157 | ~v4_pre_topc(B_157, '#skF_2') | ~m1_subset_1(B_157, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_704])).
% 3.66/1.68  tff(c_742, plain, (![B_160]: (k2_pre_topc('#skF_2', B_160)=B_160 | ~v4_pre_topc(B_160, '#skF_2') | ~m1_subset_1(B_160, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_711])).
% 3.66/1.68  tff(c_749, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_77, c_742])).
% 3.66/1.68  tff(c_757, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_749])).
% 3.66/1.68  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.66/1.68  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.66/1.68  tff(c_55, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.66/1.68  tff(c_652, plain, (![A_144, B_145, C_146]: (k9_subset_1(A_144, B_145, C_146)=k3_xboole_0(B_145, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.66/1.68  tff(c_661, plain, (![A_9, B_145]: (k9_subset_1(A_9, B_145, A_9)=k3_xboole_0(B_145, A_9))), inference(resolution, [status(thm)], [c_55, c_652])).
% 3.66/1.68  tff(c_1034, plain, (![A_194, B_195]: (v1_tops_1(k3_subset_1(u1_struct_0(A_194), B_195), A_194) | ~v3_tops_1(B_195, A_194) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.66/1.68  tff(c_1037, plain, (![B_195]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_195), '#skF_2') | ~v3_tops_1(B_195, '#skF_2') | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_1034])).
% 3.66/1.68  tff(c_1039, plain, (![B_195]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_195), '#skF_2') | ~v3_tops_1(B_195, '#skF_2') | ~m1_subset_1(B_195, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_76, c_1037])).
% 3.66/1.68  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.68  tff(c_775, plain, (![A_164, B_165]: (k2_pre_topc(A_164, B_165)=k2_struct_0(A_164) | ~v1_tops_1(B_165, A_164) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.66/1.68  tff(c_1362, plain, (![A_244, B_245]: (k2_pre_topc(A_244, k3_subset_1(u1_struct_0(A_244), B_245))=k2_struct_0(A_244) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_244), B_245), A_244) | ~l1_pre_topc(A_244) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))))), inference(resolution, [status(thm)], [c_14, c_775])).
% 3.66/1.68  tff(c_1368, plain, (![B_245]: (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), B_245))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_245), '#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_76, c_1362])).
% 3.66/1.68  tff(c_1392, plain, (![B_249]: (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_249))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_249), '#skF_2') | ~m1_subset_1(B_249, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_76, c_1368])).
% 3.66/1.68  tff(c_1397, plain, (![B_250]: (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_250))=k2_struct_0('#skF_2') | ~v3_tops_1(B_250, '#skF_2') | ~m1_subset_1(B_250, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1039, c_1392])).
% 3.66/1.68  tff(c_1404, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v3_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_77, c_1397])).
% 3.66/1.68  tff(c_1412, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_1404])).
% 3.66/1.68  tff(c_1234, plain, (![A_225, B_226]: (k9_subset_1(u1_struct_0(A_225), k2_pre_topc(A_225, B_226), k2_pre_topc(A_225, k3_subset_1(u1_struct_0(A_225), B_226)))=k2_tops_1(A_225, B_226) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.66/1.68  tff(c_1246, plain, (![B_226]: (k9_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', B_226), k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), B_226)))=k2_tops_1('#skF_2', B_226) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_1234])).
% 3.66/1.68  tff(c_1255, plain, (![B_226]: (k9_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', B_226), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_226)))=k2_tops_1('#skF_2', B_226) | ~m1_subset_1(B_226, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_76, c_76, c_1246])).
% 3.66/1.68  tff(c_1421, plain, (k9_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), k2_struct_0('#skF_2'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1412, c_1255])).
% 3.66/1.68  tff(c_1428, plain, (k2_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_737, c_757, c_661, c_1421])).
% 3.66/1.68  tff(c_1430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_1428])).
% 3.66/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.68  
% 3.66/1.68  Inference rules
% 3.66/1.68  ----------------------
% 3.66/1.68  #Ref     : 0
% 3.66/1.68  #Sup     : 307
% 3.66/1.68  #Fact    : 0
% 3.66/1.68  #Define  : 0
% 3.66/1.68  #Split   : 14
% 3.66/1.68  #Chain   : 0
% 3.66/1.68  #Close   : 0
% 3.66/1.68  
% 3.66/1.68  Ordering : KBO
% 3.66/1.68  
% 3.66/1.68  Simplification rules
% 3.66/1.68  ----------------------
% 3.66/1.68  #Subsume      : 43
% 3.66/1.68  #Demod        : 111
% 3.66/1.68  #Tautology    : 94
% 3.66/1.68  #SimpNegUnit  : 10
% 3.66/1.68  #BackRed      : 2
% 3.66/1.68  
% 3.66/1.68  #Partial instantiations: 0
% 3.66/1.68  #Strategies tried      : 1
% 3.66/1.68  
% 3.66/1.68  Timing (in seconds)
% 3.66/1.68  ----------------------
% 3.66/1.68  Preprocessing        : 0.35
% 3.66/1.68  Parsing              : 0.20
% 3.66/1.68  CNF conversion       : 0.02
% 3.66/1.68  Main loop            : 0.52
% 3.66/1.68  Inferencing          : 0.19
% 3.66/1.68  Reduction            : 0.15
% 3.66/1.68  Demodulation         : 0.10
% 3.66/1.68  BG Simplification    : 0.03
% 3.66/1.68  Subsumption          : 0.11
% 3.66/1.68  Abstraction          : 0.03
% 3.66/1.68  MUC search           : 0.00
% 3.66/1.68  Cooper               : 0.00
% 3.66/1.68  Total                : 0.91
% 3.66/1.68  Index Insertion      : 0.00
% 3.66/1.68  Index Deletion       : 0.00
% 3.66/1.68  Index Matching       : 0.00
% 3.66/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
