%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1392+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:53 EST 2020

% Result     : Theorem 34.79s
% Output     : CNFRefutation 35.32s
% Verified   : 
% Statistics : Number of formulae       :  245 (6559 expanded)
%              Number of leaves         :   42 (2249 expanded)
%              Depth                    :   33
%              Number of atoms          :  701 (19070 expanded)
%              Number of equality atoms :    8 (1567 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_connsp_1 > m1_connsp_2 > v3_pre_topc > v3_connsp_1 > r2_hidden > r1_tarski > r1_connsp_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_connsp_2 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_connsp_2,type,(
    v1_connsp_2: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_connsp_2,type,(
    r1_connsp_2: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r3_connsp_1,type,(
    r3_connsp_1: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v3_connsp_1,type,(
    v3_connsp_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( v1_connsp_2(A)
         => ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_connsp_1(B,A)
               => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_connsp_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_connsp_1(B,A)
                  & r1_tarski(B,C) )
               => r3_connsp_1(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_connsp_2)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_175,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_connsp_2(A,B)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( m1_connsp_2(C,A,B)
                        & r3_connsp_1(A,C,D)
                        & r2_hidden(B,D) )
                     => m1_connsp_2(D,A,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_connsp_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_connsp_2(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_connsp_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_connsp_2)).

tff(c_60,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_28,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_76,plain,(
    ! [A_75] :
      ( u1_struct_0(A_75) = k2_struct_0(A_75)
      | ~ l1_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    ! [A_76] :
      ( u1_struct_0(A_76) = k2_struct_0(A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_85,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_81])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_86,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_64])).

tff(c_225,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k1_tops_1(A_111,B_112),B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_235,plain,(
    ! [B_112] :
      ( r1_tarski(k1_tops_1('#skF_5',B_112),B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_225])).

tff(c_241,plain,(
    ! [B_113] :
      ( r1_tarski(k1_tops_1('#skF_5',B_113),B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_235])).

tff(c_255,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_241])).

tff(c_92,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(A_79,B_80)
      | ~ m1_subset_1(A_79,k1_zfmisc_1(B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_100,plain,(
    r1_tarski('#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_86,c_92])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12),A_11)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_157,plain,(
    ! [C_90,B_91,A_92] :
      ( r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_191,plain,(
    ! [A_103,B_104,B_105] :
      ( r2_hidden('#skF_1'(A_103,B_104),B_105)
      | ~ r1_tarski(A_103,B_105)
      | r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_18,c_157])).

tff(c_14,plain,(
    ! [C_15,B_12,A_11] :
      ( r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_341,plain,(
    ! [A_134,B_135,B_136,B_137] :
      ( r2_hidden('#skF_1'(A_134,B_135),B_136)
      | ~ r1_tarski(B_137,B_136)
      | ~ r1_tarski(A_134,B_137)
      | r1_tarski(A_134,B_135) ) ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_372,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_1'(A_138,B_139),k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_138,'#skF_6')
      | r1_tarski(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_100,c_341])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_1'(A_11,B_12),B_12)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_393,plain,(
    ! [A_138] :
      ( ~ r1_tarski(A_138,'#skF_6')
      | r1_tarski(A_138,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_372,c_16])).

tff(c_52,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(A_57,k1_zfmisc_1(B_58))
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_254,plain,(
    ! [A_57] :
      ( r1_tarski(k1_tops_1('#skF_5',A_57),A_57)
      | ~ r1_tarski(A_57,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_52,c_241])).

tff(c_513,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_1'(A_156,B_157),'#skF_6')
      | ~ r1_tarski(A_156,k1_tops_1('#skF_5','#skF_6'))
      | r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_255,c_341])).

tff(c_529,plain,(
    ! [A_158] :
      ( ~ r1_tarski(A_158,k1_tops_1('#skF_5','#skF_6'))
      | r1_tarski(A_158,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_513,c_16])).

tff(c_548,plain,
    ( r1_tarski(k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6')),'#skF_6')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_6'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_254,c_529])).

tff(c_570,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5','#skF_6'),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_573,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_393,c_570])).

tff(c_577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_573])).

tff(c_579,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_6'),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_70,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_578,plain,(
    r1_tarski(k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_594,plain,
    ( k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_578,c_2])).

tff(c_597,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_594])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_102,plain,(
    ! [A_82] :
      ( m1_subset_1(k2_struct_0(A_82),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_108,plain,
    ( m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_102])).

tff(c_115,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_118,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_118])).

tff(c_124,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_26,plain,(
    ! [A_20] :
      ( m1_subset_1(k2_struct_0(A_20),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_237,plain,(
    ! [A_20] :
      ( r1_tarski(k1_tops_1(A_20,k2_struct_0(A_20)),k2_struct_0(A_20))
      | ~ l1_pre_topc(A_20)
      | ~ l1_struct_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_225])).

tff(c_62,plain,(
    v3_connsp_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1786,plain,(
    ! [A_285,C_286,B_287] :
      ( r3_connsp_1(A_285,C_286,B_287)
      | ~ r1_tarski(B_287,C_286)
      | ~ v3_connsp_1(B_287,A_285)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1803,plain,(
    ! [C_286,B_287] :
      ( r3_connsp_1('#skF_5',C_286,B_287)
      | ~ r1_tarski(B_287,C_286)
      | ~ v3_connsp_1(B_287,'#skF_5')
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_1786])).

tff(c_1811,plain,(
    ! [C_286,B_287] :
      ( r3_connsp_1('#skF_5',C_286,B_287)
      | ~ r1_tarski(B_287,C_286)
      | ~ v3_connsp_1(B_287,'#skF_5')
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_287,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_85,c_1803])).

tff(c_1854,plain,(
    ! [C_291,B_292] :
      ( r3_connsp_1('#skF_5',C_291,B_292)
      | ~ r1_tarski(B_292,C_291)
      | ~ v3_connsp_1(B_292,'#skF_5')
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_292,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1811])).

tff(c_3547,plain,(
    ! [A_386,B_387] :
      ( r3_connsp_1('#skF_5',A_386,B_387)
      | ~ r1_tarski(B_387,A_386)
      | ~ v3_connsp_1(B_387,'#skF_5')
      | ~ m1_subset_1(B_387,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_386,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_52,c_1854])).

tff(c_3566,plain,(
    ! [A_386] :
      ( r3_connsp_1('#skF_5',A_386,'#skF_6')
      | ~ r1_tarski('#skF_6',A_386)
      | ~ v3_connsp_1('#skF_6','#skF_5')
      | ~ r1_tarski(A_386,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_86,c_3547])).

tff(c_3576,plain,(
    ! [A_388] :
      ( r3_connsp_1('#skF_5',A_388,'#skF_6')
      | ~ r1_tarski('#skF_6',A_388)
      | ~ r1_tarski(A_388,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3566])).

tff(c_3629,plain,
    ( r3_connsp_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_6')
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_237,c_3576])).

tff(c_3669,plain,
    ( r3_connsp_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_6')
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_3629])).

tff(c_3688,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_3669])).

tff(c_50,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_109,plain,(
    ! [A_82] :
      ( r1_tarski(k2_struct_0(A_82),u1_struct_0(A_82))
      | ~ l1_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_102,c_50])).

tff(c_803,plain,(
    ! [A_194,B_195,A_196] :
      ( r2_hidden('#skF_1'(A_194,B_195),u1_struct_0(A_196))
      | ~ r1_tarski(A_194,k2_struct_0(A_196))
      | r1_tarski(A_194,B_195)
      | ~ l1_struct_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_109,c_341])).

tff(c_820,plain,(
    ! [A_197,A_198] :
      ( ~ r1_tarski(A_197,k2_struct_0(A_198))
      | r1_tarski(A_197,u1_struct_0(A_198))
      | ~ l1_struct_0(A_198) ) ),
    inference(resolution,[status(thm)],[c_803,c_16])).

tff(c_211,plain,(
    ! [A_103,B_104,B_12,B_105] :
      ( r2_hidden('#skF_1'(A_103,B_104),B_12)
      | ~ r1_tarski(B_105,B_12)
      | ~ r1_tarski(A_103,B_105)
      | r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_4356,plain,(
    ! [A_440,B_441,A_442,A_443] :
      ( r2_hidden('#skF_1'(A_440,B_441),u1_struct_0(A_442))
      | ~ r1_tarski(A_440,A_443)
      | r1_tarski(A_440,B_441)
      | ~ r1_tarski(A_443,k2_struct_0(A_442))
      | ~ l1_struct_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_820,c_211])).

tff(c_4527,plain,(
    ! [B_446,A_447] :
      ( r2_hidden('#skF_1'('#skF_6',B_446),u1_struct_0(A_447))
      | r1_tarski('#skF_6',B_446)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0(A_447))
      | ~ l1_struct_0(A_447) ) ),
    inference(resolution,[status(thm)],[c_100,c_4356])).

tff(c_4538,plain,(
    ! [B_446] :
      ( r2_hidden('#skF_1'('#skF_6',B_446),k2_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_446)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
      | ~ l1_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_4527])).

tff(c_4544,plain,(
    ! [B_448] :
      ( r2_hidden('#skF_1'('#skF_6',B_448),k2_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_448) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_6,c_4538])).

tff(c_161,plain,(
    ! [A_93,C_94,B_95] :
      ( m1_subset_1(A_93,C_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(C_94))
      | ~ r2_hidden(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_171,plain,(
    ! [A_93,A_20] :
      ( m1_subset_1(A_93,u1_struct_0(A_20))
      | ~ r2_hidden(A_93,k2_struct_0(A_20))
      | ~ l1_struct_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_161])).

tff(c_4550,plain,(
    ! [B_448] :
      ( m1_subset_1('#skF_1'('#skF_6',B_448),u1_struct_0('#skF_5'))
      | ~ l1_struct_0('#skF_5')
      | r1_tarski('#skF_6',B_448) ) ),
    inference(resolution,[status(thm)],[c_4544,c_171])).

tff(c_4565,plain,(
    ! [B_448] :
      ( m1_subset_1('#skF_1'('#skF_6',B_448),k2_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_448) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_85,c_4550])).

tff(c_4568,plain,(
    ! [B_448,B_12] :
      ( r2_hidden('#skF_1'('#skF_6',B_448),B_12)
      | ~ r1_tarski(k2_struct_0('#skF_5'),B_12)
      | r1_tarski('#skF_6',B_448) ) ),
    inference(resolution,[status(thm)],[c_4544,c_14])).

tff(c_30,plain,(
    ! [A_22] :
      ( v3_pre_topc(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_123,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_173,plain,(
    ! [A_93] :
      ( m1_subset_1(A_93,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_93,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_86,c_161])).

tff(c_1659,plain,(
    ! [B_275,A_276,C_277] :
      ( m1_connsp_2(B_275,A_276,C_277)
      | ~ r2_hidden(C_277,B_275)
      | ~ v3_pre_topc(B_275,A_276)
      | ~ m1_subset_1(C_277,u1_struct_0(A_276))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1673,plain,(
    ! [B_275,C_277] :
      ( m1_connsp_2(B_275,'#skF_5',C_277)
      | ~ r2_hidden(C_277,B_275)
      | ~ v3_pre_topc(B_275,'#skF_5')
      | ~ m1_subset_1(C_277,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_1659])).

tff(c_1680,plain,(
    ! [B_275,C_277] :
      ( m1_connsp_2(B_275,'#skF_5',C_277)
      | ~ r2_hidden(C_277,B_275)
      | ~ v3_pre_topc(B_275,'#skF_5')
      | ~ m1_subset_1(C_277,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_85,c_1673])).

tff(c_1683,plain,(
    ! [B_279,C_280] :
      ( m1_connsp_2(B_279,'#skF_5',C_280)
      | ~ r2_hidden(C_280,B_279)
      | ~ v3_pre_topc(B_279,'#skF_5')
      | ~ m1_subset_1(C_280,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1680])).

tff(c_3171,plain,(
    ! [B_366,A_367] :
      ( m1_connsp_2(B_366,'#skF_5',A_367)
      | ~ r2_hidden(A_367,B_366)
      | ~ v3_pre_topc(B_366,'#skF_5')
      | ~ m1_subset_1(B_366,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden(A_367,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_173,c_1683])).

tff(c_3195,plain,(
    ! [A_367] :
      ( m1_connsp_2(k2_struct_0('#skF_5'),'#skF_5',A_367)
      | ~ r2_hidden(A_367,k2_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | ~ r2_hidden(A_367,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_123,c_3171])).

tff(c_3198,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3195])).

tff(c_3201,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_3198])).

tff(c_3205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3201])).

tff(c_3207,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3195])).

tff(c_4571,plain,(
    ! [B_449] :
      ( m1_subset_1('#skF_1'('#skF_6',B_449),k2_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_85,c_4550])).

tff(c_1681,plain,(
    ! [B_275,C_277] :
      ( m1_connsp_2(B_275,'#skF_5',C_277)
      | ~ r2_hidden(C_277,B_275)
      | ~ v3_pre_topc(B_275,'#skF_5')
      | ~ m1_subset_1(C_277,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1680])).

tff(c_4755,plain,(
    ! [B_458,B_459] :
      ( m1_connsp_2(B_458,'#skF_5','#skF_1'('#skF_6',B_459))
      | ~ r2_hidden('#skF_1'('#skF_6',B_459),B_458)
      | ~ v3_pre_topc(B_458,'#skF_5')
      | ~ m1_subset_1(B_458,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | r1_tarski('#skF_6',B_459) ) ),
    inference(resolution,[status(thm)],[c_4571,c_1681])).

tff(c_4769,plain,(
    ! [B_459] :
      ( m1_connsp_2(k2_struct_0('#skF_5'),'#skF_5','#skF_1'('#skF_6',B_459))
      | ~ r2_hidden('#skF_1'('#skF_6',B_459),k2_struct_0('#skF_5'))
      | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
      | r1_tarski('#skF_6',B_459) ) ),
    inference(resolution,[status(thm)],[c_123,c_4755])).

tff(c_4781,plain,(
    ! [B_459] :
      ( m1_connsp_2(k2_struct_0('#skF_5'),'#skF_5','#skF_1'('#skF_6',B_459))
      | ~ r2_hidden('#skF_1'('#skF_6',B_459),k2_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_459) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3207,c_4769])).

tff(c_1463,plain,(
    ! [B_260,A_261,C_262] :
      ( r2_hidden(B_260,k1_tops_1(A_261,C_262))
      | ~ m1_connsp_2(C_262,A_261,B_260)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ m1_subset_1(B_260,u1_struct_0(A_261))
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4307,plain,(
    ! [B_429,A_430,A_431] :
      ( r2_hidden(B_429,k1_tops_1(A_430,A_431))
      | ~ m1_connsp_2(A_431,A_430,B_429)
      | ~ m1_subset_1(B_429,u1_struct_0(A_430))
      | ~ l1_pre_topc(A_430)
      | ~ v2_pre_topc(A_430)
      | v2_struct_0(A_430)
      | ~ r1_tarski(A_431,u1_struct_0(A_430)) ) ),
    inference(resolution,[status(thm)],[c_52,c_1463])).

tff(c_17826,plain,(
    ! [A_861,A_862,A_863] :
      ( r1_tarski(A_861,k1_tops_1(A_862,A_863))
      | ~ m1_connsp_2(A_863,A_862,'#skF_1'(A_861,k1_tops_1(A_862,A_863)))
      | ~ m1_subset_1('#skF_1'(A_861,k1_tops_1(A_862,A_863)),u1_struct_0(A_862))
      | ~ l1_pre_topc(A_862)
      | ~ v2_pre_topc(A_862)
      | v2_struct_0(A_862)
      | ~ r1_tarski(A_863,u1_struct_0(A_862)) ) ),
    inference(resolution,[status(thm)],[c_4307,c_16])).

tff(c_17856,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4781,c_17826])).

tff(c_17910,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_85,c_70,c_68,c_85,c_17856])).

tff(c_17911,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3688,c_72,c_17910])).

tff(c_17932,plain,(
    ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_17911])).

tff(c_17935,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4568,c_17932])).

tff(c_17971,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17935])).

tff(c_17973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3688,c_17971])).

tff(c_17974,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_17911])).

tff(c_17978,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_4565,c_17974])).

tff(c_17994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3688,c_17978])).

tff(c_17996,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_3669])).

tff(c_172,plain,(
    ! [A_93,B_58,A_57] :
      ( m1_subset_1(A_93,B_58)
      | ~ r2_hidden(A_93,A_57)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_52,c_161])).

tff(c_615,plain,(
    ! [A_168,B_169,B_170,B_171] :
      ( m1_subset_1('#skF_1'(A_168,B_169),B_170)
      | ~ r1_tarski(B_171,B_170)
      | ~ r1_tarski(A_168,B_171)
      | r1_tarski(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_191,c_172])).

tff(c_649,plain,(
    ! [A_168,B_169,A_57] :
      ( m1_subset_1('#skF_1'(A_168,B_169),A_57)
      | ~ r1_tarski(A_168,k1_tops_1('#skF_5',A_57))
      | r1_tarski(A_168,B_169)
      | ~ r1_tarski(A_57,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_254,c_615])).

tff(c_18024,plain,(
    ! [B_169] :
      ( m1_subset_1('#skF_1'('#skF_6',B_169),k2_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_169)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_17996,c_649])).

tff(c_18047,plain,(
    ! [B_169] :
      ( m1_subset_1('#skF_1'('#skF_6',B_169),k2_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18024])).

tff(c_160,plain,(
    ! [A_11,B_12,B_91] :
      ( r2_hidden('#skF_1'(A_11,B_12),B_91)
      | ~ r1_tarski(A_11,B_91)
      | r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_157])).

tff(c_1486,plain,(
    ! [B_260,A_261,A_57] :
      ( r2_hidden(B_260,k1_tops_1(A_261,A_57))
      | ~ m1_connsp_2(A_57,A_261,B_260)
      | ~ m1_subset_1(B_260,u1_struct_0(A_261))
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261)
      | ~ r1_tarski(A_57,u1_struct_0(A_261)) ) ),
    inference(resolution,[status(thm)],[c_52,c_1463])).

tff(c_303,plain,(
    ! [A_127,B_128] :
      ( v3_pre_topc(k1_tops_1(A_127,B_128),A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_313,plain,(
    ! [B_128] :
      ( v3_pre_topc(k1_tops_1('#skF_5',B_128),'#skF_5')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_303])).

tff(c_319,plain,(
    ! [B_129] :
      ( v3_pre_topc(k1_tops_1('#skF_5',B_129),'#skF_5')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_313])).

tff(c_337,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_319])).

tff(c_59847,plain,(
    ! [A_2048,A_2049] :
      ( r3_connsp_1('#skF_5',A_2048,A_2049)
      | ~ r1_tarski(A_2049,A_2048)
      | ~ v3_connsp_1(A_2049,'#skF_5')
      | ~ r1_tarski(A_2048,k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_2049,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_52,c_3547])).

tff(c_63779,plain,(
    ! [A_2154] :
      ( r3_connsp_1('#skF_5',k1_tops_1('#skF_5','#skF_6'),A_2154)
      | ~ r1_tarski(A_2154,k1_tops_1('#skF_5','#skF_6'))
      | ~ v3_connsp_1(A_2154,'#skF_5')
      | ~ r1_tarski(A_2154,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_579,c_59847])).

tff(c_36,plain,(
    ! [D_55,A_32,B_46,C_53] :
      ( m1_connsp_2(D_55,A_32,B_46)
      | ~ r2_hidden(B_46,D_55)
      | ~ r3_connsp_1(A_32,C_53,D_55)
      | ~ m1_connsp_2(C_53,A_32,B_46)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ r1_connsp_2(A_32,B_46)
      | ~ m1_subset_1(B_46,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_63781,plain,(
    ! [A_2154,B_46] :
      ( m1_connsp_2(A_2154,'#skF_5',B_46)
      | ~ r2_hidden(B_46,A_2154)
      | ~ m1_connsp_2(k1_tops_1('#skF_5','#skF_6'),'#skF_5',B_46)
      | ~ m1_subset_1(A_2154,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k1_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_connsp_2('#skF_5',B_46)
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_2154,k1_tops_1('#skF_5','#skF_6'))
      | ~ v3_connsp_1(A_2154,'#skF_5')
      | ~ r1_tarski(A_2154,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_63779,c_36])).

tff(c_63784,plain,(
    ! [A_2154,B_46] :
      ( m1_connsp_2(A_2154,'#skF_5',B_46)
      | ~ r2_hidden(B_46,A_2154)
      | ~ m1_connsp_2(k1_tops_1('#skF_5','#skF_6'),'#skF_5',B_46)
      | ~ m1_subset_1(A_2154,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k1_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_connsp_2('#skF_5',B_46)
      | ~ m1_subset_1(B_46,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_2154,k1_tops_1('#skF_5','#skF_6'))
      | ~ v3_connsp_1(A_2154,'#skF_5')
      | ~ r1_tarski(A_2154,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_85,c_85,c_85,c_63781])).

tff(c_63785,plain,(
    ! [A_2154,B_46] :
      ( m1_connsp_2(A_2154,'#skF_5',B_46)
      | ~ r2_hidden(B_46,A_2154)
      | ~ m1_connsp_2(k1_tops_1('#skF_5','#skF_6'),'#skF_5',B_46)
      | ~ m1_subset_1(A_2154,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k1_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_connsp_2('#skF_5',B_46)
      | ~ m1_subset_1(B_46,k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_2154,k1_tops_1('#skF_5','#skF_6'))
      | ~ v3_connsp_1(A_2154,'#skF_5')
      | ~ r1_tarski(A_2154,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_63784])).

tff(c_64140,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_63785])).

tff(c_64143,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5','#skF_6'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_64140])).

tff(c_64147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_64143])).

tff(c_64149,plain,(
    m1_subset_1(k1_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_63785])).

tff(c_18063,plain,(
    ! [B_866] :
      ( m1_subset_1('#skF_1'('#skF_6',B_866),k2_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18024])).

tff(c_18076,plain,(
    ! [B_275,B_866] :
      ( m1_connsp_2(B_275,'#skF_5','#skF_1'('#skF_6',B_866))
      | ~ r2_hidden('#skF_1'('#skF_6',B_866),B_275)
      | ~ v3_pre_topc(B_275,'#skF_5')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | r1_tarski('#skF_6',B_866) ) ),
    inference(resolution,[status(thm)],[c_18063,c_1681])).

tff(c_64151,plain,(
    ! [B_866] :
      ( m1_connsp_2(k1_tops_1('#skF_5','#skF_6'),'#skF_5','#skF_1'('#skF_6',B_866))
      | ~ r2_hidden('#skF_1'('#skF_6',B_866),k1_tops_1('#skF_5','#skF_6'))
      | ~ v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5')
      | r1_tarski('#skF_6',B_866) ) ),
    inference(resolution,[status(thm)],[c_64149,c_18076])).

tff(c_64174,plain,(
    ! [B_866] :
      ( m1_connsp_2(k1_tops_1('#skF_5','#skF_6'),'#skF_5','#skF_1'('#skF_6',B_866))
      | ~ r2_hidden('#skF_1'('#skF_6',B_866),k1_tops_1('#skF_5','#skF_6'))
      | r1_tarski('#skF_6',B_866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_64151])).

tff(c_18590,plain,(
    ! [B_884,A_885,A_886] :
      ( r2_hidden(B_884,k1_tops_1(A_885,A_886))
      | ~ m1_connsp_2(A_886,A_885,B_884)
      | ~ m1_subset_1(B_884,u1_struct_0(A_885))
      | ~ l1_pre_topc(A_885)
      | ~ v2_pre_topc(A_885)
      | v2_struct_0(A_885)
      | ~ r1_tarski(A_886,u1_struct_0(A_885)) ) ),
    inference(resolution,[status(thm)],[c_52,c_1463])).

tff(c_71544,plain,(
    ! [A_2375,A_2376,A_2377] :
      ( r1_tarski(A_2375,k1_tops_1(A_2376,A_2377))
      | ~ m1_connsp_2(A_2377,A_2376,'#skF_1'(A_2375,k1_tops_1(A_2376,A_2377)))
      | ~ m1_subset_1('#skF_1'(A_2375,k1_tops_1(A_2376,A_2377)),u1_struct_0(A_2376))
      | ~ l1_pre_topc(A_2376)
      | ~ v2_pre_topc(A_2376)
      | v2_struct_0(A_2376)
      | ~ r1_tarski(A_2377,u1_struct_0(A_2376)) ) ),
    inference(resolution,[status(thm)],[c_18590,c_16])).

tff(c_71556,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k1_tops_1('#skF_5','#skF_6'))
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_64174,c_71544])).

tff(c_71616,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k1_tops_1('#skF_5','#skF_6'))
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_85,c_70,c_68,c_85,c_71556])).

tff(c_71617,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k2_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k1_tops_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_72,c_71616])).

tff(c_77686,plain,(
    ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_71617])).

tff(c_77698,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))))
    | ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1486,c_77686])).

tff(c_77725,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))))
    | ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_85,c_70,c_68,c_85,c_77698])).

tff(c_77726,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))))
    | ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_77725])).

tff(c_78156,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_77726])).

tff(c_78159,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_18047,c_78156])).

tff(c_78175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_78159])).

tff(c_78176,plain,(
    ~ m1_connsp_2('#skF_6','#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_77726])).

tff(c_253,plain,(
    r1_tarski(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_123,c_241])).

tff(c_2736,plain,(
    ! [A_339,B_340,A_341] :
      ( r2_hidden('#skF_1'(A_339,B_340),A_341)
      | ~ r1_tarski(A_339,k1_tops_1('#skF_5',A_341))
      | r1_tarski(A_339,B_340)
      | ~ r1_tarski(A_341,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_254,c_341])).

tff(c_2775,plain,(
    ! [A_342,A_343] :
      ( ~ r1_tarski(A_342,k1_tops_1('#skF_5',A_343))
      | r1_tarski(A_342,A_343)
      | ~ r1_tarski(A_343,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2736,c_16])).

tff(c_2798,plain,(
    ! [A_343] :
      ( r1_tarski(k1_tops_1('#skF_5',k1_tops_1('#skF_5',A_343)),A_343)
      | ~ r1_tarski(A_343,k2_struct_0('#skF_5'))
      | ~ r1_tarski(k1_tops_1('#skF_5',A_343),k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_254,c_2775])).

tff(c_3592,plain,
    ( r3_connsp_1('#skF_5',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),'#skF_6')
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))))
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ r1_tarski(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2798,c_3576])).

tff(c_3654,plain,
    ( r3_connsp_1('#skF_5',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))),'#skF_6')
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_6,c_3592])).

tff(c_18742,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_3654])).

tff(c_18055,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103,B_104),k1_tops_1('#skF_5',k2_struct_0('#skF_5')))
      | ~ r1_tarski(A_103,'#skF_6')
      | r1_tarski(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_17996,c_211])).

tff(c_335,plain,(
    v3_pre_topc(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_123,c_319])).

tff(c_17995,plain,(
    r3_connsp_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3669])).

tff(c_18058,plain,(
    ! [B_46] :
      ( m1_connsp_2('#skF_6','#skF_5',B_46)
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_connsp_2(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_5',B_46)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_connsp_2('#skF_5',B_46)
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_17995,c_36])).

tff(c_18061,plain,(
    ! [B_46] :
      ( m1_connsp_2('#skF_6','#skF_5',B_46)
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_connsp_2(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_5',B_46)
      | ~ m1_subset_1(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_connsp_2('#skF_5',B_46)
      | ~ m1_subset_1(B_46,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_85,c_85,c_86,c_85,c_18058])).

tff(c_18062,plain,(
    ! [B_46] :
      ( m1_connsp_2('#skF_6','#skF_5',B_46)
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_connsp_2(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_5',B_46)
      | ~ m1_subset_1(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r1_connsp_2('#skF_5',B_46)
      | ~ m1_subset_1(B_46,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_18061])).

tff(c_18209,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_18062])).

tff(c_18212,plain,(
    ~ r1_tarski(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_18209])).

tff(c_18216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_18212])).

tff(c_18218,plain,(
    m1_subset_1(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_18062])).

tff(c_20997,plain,(
    ! [B_1004,B_1005] :
      ( m1_connsp_2(B_1004,'#skF_5','#skF_1'('#skF_6',B_1005))
      | ~ r2_hidden('#skF_1'('#skF_6',B_1005),B_1004)
      | ~ v3_pre_topc(B_1004,'#skF_5')
      | ~ m1_subset_1(B_1004,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | r1_tarski('#skF_6',B_1005) ) ),
    inference(resolution,[status(thm)],[c_18063,c_1681])).

tff(c_20999,plain,(
    ! [B_1005] :
      ( m1_connsp_2(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_5','#skF_1'('#skF_6',B_1005))
      | ~ r2_hidden('#skF_1'('#skF_6',B_1005),k1_tops_1('#skF_5',k2_struct_0('#skF_5')))
      | ~ v3_pre_topc(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_5')
      | r1_tarski('#skF_6',B_1005) ) ),
    inference(resolution,[status(thm)],[c_18218,c_20997])).

tff(c_41927,plain,(
    ! [B_1620] :
      ( m1_connsp_2(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_5','#skF_1'('#skF_6',B_1620))
      | ~ r2_hidden('#skF_1'('#skF_6',B_1620),k1_tops_1('#skF_5',k2_struct_0('#skF_5')))
      | r1_tarski('#skF_6',B_1620) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_20999])).

tff(c_18612,plain,(
    ! [A_11,A_885,A_886] :
      ( r1_tarski(A_11,k1_tops_1(A_885,A_886))
      | ~ m1_connsp_2(A_886,A_885,'#skF_1'(A_11,k1_tops_1(A_885,A_886)))
      | ~ m1_subset_1('#skF_1'(A_11,k1_tops_1(A_885,A_886)),u1_struct_0(A_885))
      | ~ l1_pre_topc(A_885)
      | ~ v2_pre_topc(A_885)
      | v2_struct_0(A_885)
      | ~ r1_tarski(A_886,u1_struct_0(A_885)) ) ),
    inference(resolution,[status(thm)],[c_18590,c_16])).

tff(c_41932,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ r1_tarski(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))),k1_tops_1('#skF_5',k2_struct_0('#skF_5')))
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_41927,c_18612])).

tff(c_41960,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))),k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))),k1_tops_1('#skF_5',k2_struct_0('#skF_5')))
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_85,c_70,c_68,c_85,c_41932])).

tff(c_41961,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))),k2_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))),k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_18742,c_72,c_41960])).

tff(c_57075,plain,(
    ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))),k1_tops_1('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_41961])).

tff(c_57108,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_18055,c_57075])).

tff(c_57151,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57108])).

tff(c_57153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18742,c_57151])).

tff(c_57154,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_41961])).

tff(c_57158,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_18047,c_57154])).

tff(c_57174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18742,c_57158])).

tff(c_57176,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_3654])).

tff(c_78177,plain,(
    m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_77726])).

tff(c_66,plain,(
    v1_connsp_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_401,plain,(
    ! [A_141,B_142] :
      ( r1_connsp_2(A_141,B_142)
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ v1_connsp_2(A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_414,plain,(
    ! [B_142] :
      ( r1_connsp_2('#skF_5',B_142)
      | ~ m1_subset_1(B_142,k2_struct_0('#skF_5'))
      | ~ v1_connsp_2('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_401])).

tff(c_419,plain,(
    ! [B_142] :
      ( r1_connsp_2('#skF_5',B_142)
      | ~ m1_subset_1(B_142,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_414])).

tff(c_420,plain,(
    ! [B_142] :
      ( r1_connsp_2('#skF_5',B_142)
      | ~ m1_subset_1(B_142,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_419])).

tff(c_78208,plain,(
    r1_connsp_2('#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6')))) ),
    inference(resolution,[status(thm)],[c_78177,c_420])).

tff(c_1269,plain,(
    ! [C_243,A_244,B_245] :
      ( m1_connsp_2(C_243,A_244,B_245)
      | ~ r2_hidden(B_245,k1_tops_1(A_244,C_243))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ m1_subset_1(B_245,u1_struct_0(A_244))
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69524,plain,(
    ! [C_2327,A_2328,A_2329,B_2330] :
      ( m1_connsp_2(C_2327,A_2328,'#skF_1'(A_2329,B_2330))
      | ~ m1_subset_1(C_2327,k1_zfmisc_1(u1_struct_0(A_2328)))
      | ~ m1_subset_1('#skF_1'(A_2329,B_2330),u1_struct_0(A_2328))
      | ~ l1_pre_topc(A_2328)
      | ~ v2_pre_topc(A_2328)
      | v2_struct_0(A_2328)
      | ~ r1_tarski(A_2329,k1_tops_1(A_2328,C_2327))
      | r1_tarski(A_2329,B_2330) ) ),
    inference(resolution,[status(thm)],[c_160,c_1269])).

tff(c_99926,plain,(
    ! [A_3000,A_3001,A_3002,B_3003] :
      ( m1_connsp_2(A_3000,A_3001,'#skF_1'(A_3002,B_3003))
      | ~ m1_subset_1('#skF_1'(A_3002,B_3003),u1_struct_0(A_3001))
      | ~ l1_pre_topc(A_3001)
      | ~ v2_pre_topc(A_3001)
      | v2_struct_0(A_3001)
      | ~ r1_tarski(A_3002,k1_tops_1(A_3001,A_3000))
      | r1_tarski(A_3002,B_3003)
      | ~ r1_tarski(A_3000,u1_struct_0(A_3001)) ) ),
    inference(resolution,[status(thm)],[c_52,c_69524])).

tff(c_99978,plain,(
    ! [A_3000,A_3002,B_3003] :
      ( m1_connsp_2(A_3000,'#skF_5','#skF_1'(A_3002,B_3003))
      | ~ m1_subset_1('#skF_1'(A_3002,B_3003),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_3002,k1_tops_1('#skF_5',A_3000))
      | r1_tarski(A_3002,B_3003)
      | ~ r1_tarski(A_3000,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_99926])).

tff(c_100000,plain,(
    ! [A_3000,A_3002,B_3003] :
      ( m1_connsp_2(A_3000,'#skF_5','#skF_1'(A_3002,B_3003))
      | ~ m1_subset_1('#skF_1'(A_3002,B_3003),k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_3002,k1_tops_1('#skF_5',A_3000))
      | r1_tarski(A_3002,B_3003)
      | ~ r1_tarski(A_3000,k2_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_68,c_99978])).

tff(c_100013,plain,(
    ! [A_3004,A_3005,B_3006] :
      ( m1_connsp_2(A_3004,'#skF_5','#skF_1'(A_3005,B_3006))
      | ~ m1_subset_1('#skF_1'(A_3005,B_3006),k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_3005,k1_tops_1('#skF_5',A_3004))
      | r1_tarski(A_3005,B_3006)
      | ~ r1_tarski(A_3004,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_100000])).

tff(c_100028,plain,(
    ! [A_3004] :
      ( m1_connsp_2(A_3004,'#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))))
      | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',A_3004))
      | r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6')))
      | ~ r1_tarski(A_3004,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_78177,c_100013])).

tff(c_100848,plain,(
    ! [A_3011] :
      ( m1_connsp_2(A_3011,'#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))))
      | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',A_3011))
      | ~ r1_tarski(A_3011,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_100028])).

tff(c_18217,plain,(
    ! [B_46] :
      ( m1_connsp_2('#skF_6','#skF_5',B_46)
      | ~ r2_hidden(B_46,'#skF_6')
      | ~ m1_connsp_2(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),'#skF_5',B_46)
      | ~ r1_connsp_2('#skF_5',B_46)
      | ~ m1_subset_1(B_46,k2_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_18062])).

tff(c_101148,plain,
    ( m1_connsp_2('#skF_6','#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))))
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),'#skF_6')
    | ~ r1_connsp_2('#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))))
    | ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k2_struct_0('#skF_5'))
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5',k2_struct_0('#skF_5'))))
    | ~ r1_tarski(k1_tops_1('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_100848,c_18217])).

tff(c_101453,plain,
    ( m1_connsp_2('#skF_6','#skF_5','#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))))
    | ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_57176,c_78177,c_78208,c_101148])).

tff(c_101454,plain,(
    ~ r2_hidden('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78176,c_101453])).

tff(c_101501,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_160,c_101454])).

tff(c_101525,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_101501])).

tff(c_101527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_101525])).

tff(c_101528,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_71617])).

tff(c_101575,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_18047,c_101528])).

tff(c_101591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_101575])).

tff(c_101592,plain,(
    k1_tops_1('#skF_5',k1_tops_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_594])).

tff(c_316,plain,(
    ! [A_127,A_57] :
      ( v3_pre_topc(k1_tops_1(A_127,A_57),A_127)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | ~ r1_tarski(A_57,u1_struct_0(A_127)) ) ),
    inference(resolution,[status(thm)],[c_52,c_303])).

tff(c_101599,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101592,c_316])).

tff(c_101615,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_85,c_70,c_68,c_101599])).

tff(c_101617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101615])).

%------------------------------------------------------------------------------
