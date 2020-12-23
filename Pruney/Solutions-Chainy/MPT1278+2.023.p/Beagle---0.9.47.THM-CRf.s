%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:11 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 671 expanded)
%              Number of leaves         :   44 ( 247 expanded)
%              Depth                    :   17
%              Number of atoms          :  280 (1579 expanded)
%              Number of equality atoms :   64 ( 363 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_80,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_58,plain,(
    v3_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_424,plain,(
    ! [B_109,A_110] :
      ( v2_tops_1(B_109,A_110)
      | ~ v3_tops_1(B_109,A_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_459,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | ~ v3_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_424])).

tff(c_478,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_459])).

tff(c_760,plain,(
    ! [A_135,B_136] :
      ( k1_tops_1(A_135,B_136) = k1_xboole_0
      | ~ v2_tops_1(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_798,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_760])).

tff(c_820,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_478,c_798])).

tff(c_2406,plain,(
    ! [A_236,B_237] :
      ( k1_tops_1(A_236,k1_tops_1(A_236,B_237)) = k1_tops_1(A_236,B_237)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2437,plain,
    ( k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2406])).

tff(c_2458,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_820,c_820,c_2437])).

tff(c_26,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_904,plain,(
    ! [B_140,A_141] :
      ( v2_tops_1(B_140,A_141)
      | k1_tops_1(A_141,B_140) != k1_xboole_0
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_971,plain,(
    ! [A_141] :
      ( v2_tops_1(k1_xboole_0,A_141)
      | k1_tops_1(A_141,k1_xboole_0) != k1_xboole_0
      | ~ l1_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_26,c_904])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_644,plain,(
    ! [A_123,B_124] :
      ( v3_pre_topc(k1_tops_1(A_123,B_124),A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_672,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_644])).

tff(c_692,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_672])).

tff(c_823,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_692])).

tff(c_14,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    ! [A_76,B_77] :
      ( k3_subset_1(A_76,k3_subset_1(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_184,plain,(
    ! [A_18] : k3_subset_1(A_18,k3_subset_1(A_18,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_173])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k2_subset_1(A_16) = B_17
      | ~ r1_tarski(k3_subset_1(A_16,B_17),B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_274,plain,(
    ! [B_90,A_91] :
      ( B_90 = A_91
      | ~ r1_tarski(k3_subset_1(A_91,B_90),B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_296,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93))
      | ~ v1_xboole_0(k3_subset_1(A_93,B_92)) ) ),
    inference(resolution,[status(thm)],[c_100,c_274])).

tff(c_4831,plain,(
    ! [A_341,B_342] :
      ( k3_subset_1(A_341,B_342) = A_341
      | ~ v1_xboole_0(k3_subset_1(A_341,k3_subset_1(A_341,B_342)))
      | ~ m1_subset_1(B_342,k1_zfmisc_1(A_341)) ) ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_4879,plain,(
    ! [A_18] :
      ( k3_subset_1(A_18,k1_xboole_0) = A_18
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_4831])).

tff(c_4889,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12,c_4879])).

tff(c_5142,plain,(
    ! [A_346] : k3_subset_1(A_346,A_346) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4889,c_184])).

tff(c_46,plain,(
    ! [B_37,A_35] :
      ( v4_pre_topc(B_37,A_35)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_35),B_37),A_35)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5166,plain,(
    ! [A_35] :
      ( v4_pre_topc(u1_struct_0(A_35),A_35)
      | ~ v3_pre_topc(k1_xboole_0,A_35)
      | ~ m1_subset_1(u1_struct_0(A_35),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5142,c_46])).

tff(c_5446,plain,(
    ! [A_359] :
      ( v4_pre_topc(u1_struct_0(A_359),A_359)
      | ~ v3_pre_topc(k1_xboole_0,A_359)
      | ~ l1_pre_topc(A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5166])).

tff(c_535,plain,(
    ! [A_114,B_115] :
      ( k2_pre_topc(A_114,B_115) = B_115
      | ~ v4_pre_topc(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_597,plain,(
    ! [A_114] :
      ( k2_pre_topc(A_114,u1_struct_0(A_114)) = u1_struct_0(A_114)
      | ~ v4_pre_topc(u1_struct_0(A_114),A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_70,c_535])).

tff(c_5655,plain,(
    ! [A_376] :
      ( k2_pre_topc(A_376,u1_struct_0(A_376)) = u1_struct_0(A_376)
      | ~ v3_pre_topc(k1_xboole_0,A_376)
      | ~ l1_pre_topc(A_376) ) ),
    inference(resolution,[status(thm)],[c_5446,c_597])).

tff(c_1110,plain,(
    ! [B_156,A_157] :
      ( v1_tops_1(B_156,A_157)
      | k2_pre_topc(A_157,B_156) != k2_struct_0(A_157)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1177,plain,(
    ! [A_157] :
      ( v1_tops_1(u1_struct_0(A_157),A_157)
      | k2_pre_topc(A_157,u1_struct_0(A_157)) != k2_struct_0(A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_70,c_1110])).

tff(c_4895,plain,(
    ! [A_343] : k3_subset_1(A_343,k1_xboole_0) = A_343 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12,c_4879])).

tff(c_38,plain,(
    ! [B_30,A_28] :
      ( v2_tops_1(B_30,A_28)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_28),B_30),A_28)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4932,plain,(
    ! [A_28] :
      ( v2_tops_1(k1_xboole_0,A_28)
      | ~ v1_tops_1(u1_struct_0(A_28),A_28)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4895,c_38])).

tff(c_5431,plain,(
    ! [A_357] :
      ( v2_tops_1(k1_xboole_0,A_357)
      | ~ v1_tops_1(u1_struct_0(A_357),A_357)
      | ~ l1_pre_topc(A_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4932])).

tff(c_5439,plain,(
    ! [A_157] :
      ( v2_tops_1(k1_xboole_0,A_157)
      | k2_pre_topc(A_157,u1_struct_0(A_157)) != k2_struct_0(A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_1177,c_5431])).

tff(c_5833,plain,(
    ! [A_388] :
      ( v2_tops_1(k1_xboole_0,A_388)
      | u1_struct_0(A_388) != k2_struct_0(A_388)
      | ~ l1_pre_topc(A_388)
      | ~ v3_pre_topc(k1_xboole_0,A_388)
      | ~ l1_pre_topc(A_388) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5655,c_5439])).

tff(c_5839,plain,
    ( v2_tops_1(k1_xboole_0,'#skF_3')
    | u1_struct_0('#skF_3') != k2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_823,c_5833])).

tff(c_5843,plain,
    ( v2_tops_1(k1_xboole_0,'#skF_3')
    | u1_struct_0('#skF_3') != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5839])).

tff(c_5844,plain,(
    u1_struct_0('#skF_3') != k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5843])).

tff(c_40,plain,(
    ! [A_28,B_30] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_28),B_30),A_28)
      | ~ v2_tops_1(B_30,A_28)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4928,plain,(
    ! [A_28] :
      ( v1_tops_1(u1_struct_0(A_28),A_28)
      | ~ v2_tops_1(k1_xboole_0,A_28)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4895,c_40])).

tff(c_5425,plain,(
    ! [A_355] :
      ( v1_tops_1(u1_struct_0(A_355),A_355)
      | ~ v2_tops_1(k1_xboole_0,A_355)
      | ~ l1_pre_topc(A_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4928])).

tff(c_2703,plain,(
    ! [A_250,B_251] :
      ( k2_pre_topc(A_250,B_251) = k2_struct_0(A_250)
      | ~ v1_tops_1(B_251,A_250)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2786,plain,(
    ! [A_250] :
      ( k2_pre_topc(A_250,u1_struct_0(A_250)) = k2_struct_0(A_250)
      | ~ v1_tops_1(u1_struct_0(A_250),A_250)
      | ~ l1_pre_topc(A_250) ) ),
    inference(resolution,[status(thm)],[c_70,c_2703])).

tff(c_5429,plain,(
    ! [A_355] :
      ( k2_pre_topc(A_355,u1_struct_0(A_355)) = k2_struct_0(A_355)
      | ~ v2_tops_1(k1_xboole_0,A_355)
      | ~ l1_pre_topc(A_355) ) ),
    inference(resolution,[status(thm)],[c_5425,c_2786])).

tff(c_5845,plain,(
    ! [A_389] :
      ( u1_struct_0(A_389) = k2_struct_0(A_389)
      | ~ v2_tops_1(k1_xboole_0,A_389)
      | ~ l1_pre_topc(A_389)
      | ~ v3_pre_topc(k1_xboole_0,A_389)
      | ~ l1_pre_topc(A_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5655,c_5429])).

tff(c_5851,plain,
    ( u1_struct_0('#skF_3') = k2_struct_0('#skF_3')
    | ~ v2_tops_1(k1_xboole_0,'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_823,c_5845])).

tff(c_5855,plain,
    ( u1_struct_0('#skF_3') = k2_struct_0('#skF_3')
    | ~ v2_tops_1(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5851])).

tff(c_5856,plain,(
    ~ v2_tops_1(k1_xboole_0,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_5844,c_5855])).

tff(c_5903,plain,
    ( k1_tops_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_971,c_5856])).

tff(c_5907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2458,c_5903])).

tff(c_5909,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5843])).

tff(c_2280,plain,(
    ! [A_222,B_223] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_222),B_223),A_222)
      | ~ v2_tops_1(B_223,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_183,plain,(
    k3_subset_1(u1_struct_0('#skF_3'),k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_173])).

tff(c_277,plain,
    ( k3_subset_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ r1_tarski('#skF_4',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_274])).

tff(c_483,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_486,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_18,c_483])).

tff(c_490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_486])).

tff(c_492,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_1117,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_492,c_1110])).

tff(c_1164,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1117])).

tff(c_1180,plain,(
    k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1164])).

tff(c_1447,plain,(
    ! [A_179,B_180] :
      ( k2_pre_topc(A_179,B_180) = k2_struct_0(A_179)
      | ~ v1_tops_1(B_180,A_179)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1462,plain,
    ( k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = k2_struct_0('#skF_3')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_492,c_1447])).

tff(c_1511,plain,
    ( k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = k2_struct_0('#skF_3')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1462])).

tff(c_1512,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1180,c_1511])).

tff(c_2286,plain,
    ( ~ v2_tops_1('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2280,c_1512])).

tff(c_2318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_478,c_2286])).

tff(c_2320,plain,(
    k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1164])).

tff(c_538,plain,
    ( k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_492,c_535])).

tff(c_584,plain,
    ( k2_pre_topc('#skF_3',k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_538])).

tff(c_3065,plain,
    ( k3_subset_1(u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2320,c_584])).

tff(c_3066,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3065])).

tff(c_60,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3968,plain,(
    ! [B_305,A_306] :
      ( v4_pre_topc(B_305,A_306)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_306),B_305),A_306)
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3998,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_3968])).

tff(c_4005,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_492,c_60,c_3998])).

tff(c_4007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3066,c_4005])).

tff(c_4008,plain,(
    k3_subset_1(u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3065])).

tff(c_4025,plain,(
    k3_subset_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4008,c_183])).

tff(c_5923,plain,(
    k3_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5909,c_4025])).

tff(c_4893,plain,(
    ! [A_18] : k3_subset_1(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4889,c_184])).

tff(c_6214,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5923,c_4893])).

tff(c_6238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 16:22:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.57/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.35  
% 6.57/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.35  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 6.57/2.35  
% 6.57/2.35  %Foreground sorts:
% 6.57/2.35  
% 6.57/2.35  
% 6.57/2.35  %Background operators:
% 6.57/2.35  
% 6.57/2.35  
% 6.57/2.35  %Foreground operators:
% 6.57/2.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.57/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.57/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.57/2.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.57/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.57/2.35  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 6.57/2.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.57/2.35  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 6.57/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.57/2.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.57/2.35  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 6.57/2.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.57/2.35  tff('#skF_3', type, '#skF_3': $i).
% 6.57/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.57/2.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.57/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.57/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.57/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.57/2.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.57/2.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.57/2.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.57/2.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.57/2.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.57/2.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.57/2.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.57/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.57/2.35  
% 6.83/2.38  tff(f_153, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 6.83/2.38  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 6.83/2.38  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 6.83/2.38  tff(f_112, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 6.83/2.38  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.83/2.38  tff(f_106, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.83/2.38  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.83/2.38  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.83/2.38  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.83/2.38  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.83/2.38  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.83/2.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.83/2.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.83/2.38  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 6.83/2.38  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 6.83/2.38  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.83/2.38  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 6.83/2.38  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 6.83/2.38  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.83/2.38  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.83/2.38  tff(c_58, plain, (v3_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.83/2.38  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.83/2.38  tff(c_424, plain, (![B_109, A_110]: (v2_tops_1(B_109, A_110) | ~v3_tops_1(B_109, A_110) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.83/2.38  tff(c_459, plain, (v2_tops_1('#skF_4', '#skF_3') | ~v3_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_424])).
% 6.83/2.38  tff(c_478, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_459])).
% 6.83/2.38  tff(c_760, plain, (![A_135, B_136]: (k1_tops_1(A_135, B_136)=k1_xboole_0 | ~v2_tops_1(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.83/2.38  tff(c_798, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_760])).
% 6.83/2.38  tff(c_820, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_478, c_798])).
% 6.83/2.38  tff(c_2406, plain, (![A_236, B_237]: (k1_tops_1(A_236, k1_tops_1(A_236, B_237))=k1_tops_1(A_236, B_237) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.83/2.38  tff(c_2437, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2406])).
% 6.83/2.38  tff(c_2458, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_820, c_820, c_2437])).
% 6.83/2.38  tff(c_26, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.83/2.38  tff(c_904, plain, (![B_140, A_141]: (v2_tops_1(B_140, A_141) | k1_tops_1(A_141, B_140)!=k1_xboole_0 | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.83/2.38  tff(c_971, plain, (![A_141]: (v2_tops_1(k1_xboole_0, A_141) | k1_tops_1(A_141, k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc(A_141))), inference(resolution, [status(thm)], [c_26, c_904])).
% 6.83/2.38  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.83/2.38  tff(c_644, plain, (![A_123, B_124]: (v3_pre_topc(k1_tops_1(A_123, B_124), A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.83/2.38  tff(c_672, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_644])).
% 6.83/2.38  tff(c_692, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_672])).
% 6.83/2.38  tff(c_823, plain, (v3_pre_topc(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_692])).
% 6.83/2.38  tff(c_14, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.83/2.38  tff(c_16, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.83/2.38  tff(c_70, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 6.83/2.38  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.83/2.38  tff(c_173, plain, (![A_76, B_77]: (k3_subset_1(A_76, k3_subset_1(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.83/2.38  tff(c_184, plain, (![A_18]: (k3_subset_1(A_18, k3_subset_1(A_18, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_173])).
% 6.83/2.38  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.83/2.38  tff(c_91, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.83/2.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.83/2.38  tff(c_100, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_91, c_2])).
% 6.83/2.38  tff(c_24, plain, (![A_16, B_17]: (k2_subset_1(A_16)=B_17 | ~r1_tarski(k3_subset_1(A_16, B_17), B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.83/2.38  tff(c_274, plain, (![B_90, A_91]: (B_90=A_91 | ~r1_tarski(k3_subset_1(A_91, B_90), B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 6.83/2.38  tff(c_296, plain, (![B_92, A_93]: (B_92=A_93 | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)) | ~v1_xboole_0(k3_subset_1(A_93, B_92)))), inference(resolution, [status(thm)], [c_100, c_274])).
% 6.83/2.38  tff(c_4831, plain, (![A_341, B_342]: (k3_subset_1(A_341, B_342)=A_341 | ~v1_xboole_0(k3_subset_1(A_341, k3_subset_1(A_341, B_342))) | ~m1_subset_1(B_342, k1_zfmisc_1(A_341)))), inference(resolution, [status(thm)], [c_18, c_296])).
% 6.83/2.38  tff(c_4879, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18 | ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_4831])).
% 6.83/2.38  tff(c_4889, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12, c_4879])).
% 6.83/2.38  tff(c_5142, plain, (![A_346]: (k3_subset_1(A_346, A_346)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4889, c_184])).
% 6.83/2.38  tff(c_46, plain, (![B_37, A_35]: (v4_pre_topc(B_37, A_35) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_35), B_37), A_35) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.83/2.38  tff(c_5166, plain, (![A_35]: (v4_pre_topc(u1_struct_0(A_35), A_35) | ~v3_pre_topc(k1_xboole_0, A_35) | ~m1_subset_1(u1_struct_0(A_35), k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(superposition, [status(thm), theory('equality')], [c_5142, c_46])).
% 6.83/2.38  tff(c_5446, plain, (![A_359]: (v4_pre_topc(u1_struct_0(A_359), A_359) | ~v3_pre_topc(k1_xboole_0, A_359) | ~l1_pre_topc(A_359))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5166])).
% 6.83/2.38  tff(c_535, plain, (![A_114, B_115]: (k2_pre_topc(A_114, B_115)=B_115 | ~v4_pre_topc(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.83/2.38  tff(c_597, plain, (![A_114]: (k2_pre_topc(A_114, u1_struct_0(A_114))=u1_struct_0(A_114) | ~v4_pre_topc(u1_struct_0(A_114), A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_70, c_535])).
% 6.83/2.38  tff(c_5655, plain, (![A_376]: (k2_pre_topc(A_376, u1_struct_0(A_376))=u1_struct_0(A_376) | ~v3_pre_topc(k1_xboole_0, A_376) | ~l1_pre_topc(A_376))), inference(resolution, [status(thm)], [c_5446, c_597])).
% 6.83/2.38  tff(c_1110, plain, (![B_156, A_157]: (v1_tops_1(B_156, A_157) | k2_pre_topc(A_157, B_156)!=k2_struct_0(A_157) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.83/2.38  tff(c_1177, plain, (![A_157]: (v1_tops_1(u1_struct_0(A_157), A_157) | k2_pre_topc(A_157, u1_struct_0(A_157))!=k2_struct_0(A_157) | ~l1_pre_topc(A_157))), inference(resolution, [status(thm)], [c_70, c_1110])).
% 6.83/2.38  tff(c_4895, plain, (![A_343]: (k3_subset_1(A_343, k1_xboole_0)=A_343)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12, c_4879])).
% 6.83/2.38  tff(c_38, plain, (![B_30, A_28]: (v2_tops_1(B_30, A_28) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_28), B_30), A_28) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.83/2.38  tff(c_4932, plain, (![A_28]: (v2_tops_1(k1_xboole_0, A_28) | ~v1_tops_1(u1_struct_0(A_28), A_28) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(superposition, [status(thm), theory('equality')], [c_4895, c_38])).
% 6.83/2.38  tff(c_5431, plain, (![A_357]: (v2_tops_1(k1_xboole_0, A_357) | ~v1_tops_1(u1_struct_0(A_357), A_357) | ~l1_pre_topc(A_357))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4932])).
% 6.83/2.38  tff(c_5439, plain, (![A_157]: (v2_tops_1(k1_xboole_0, A_157) | k2_pre_topc(A_157, u1_struct_0(A_157))!=k2_struct_0(A_157) | ~l1_pre_topc(A_157))), inference(resolution, [status(thm)], [c_1177, c_5431])).
% 6.83/2.38  tff(c_5833, plain, (![A_388]: (v2_tops_1(k1_xboole_0, A_388) | u1_struct_0(A_388)!=k2_struct_0(A_388) | ~l1_pre_topc(A_388) | ~v3_pre_topc(k1_xboole_0, A_388) | ~l1_pre_topc(A_388))), inference(superposition, [status(thm), theory('equality')], [c_5655, c_5439])).
% 6.83/2.38  tff(c_5839, plain, (v2_tops_1(k1_xboole_0, '#skF_3') | u1_struct_0('#skF_3')!=k2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_823, c_5833])).
% 6.83/2.38  tff(c_5843, plain, (v2_tops_1(k1_xboole_0, '#skF_3') | u1_struct_0('#skF_3')!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5839])).
% 6.83/2.38  tff(c_5844, plain, (u1_struct_0('#skF_3')!=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_5843])).
% 6.83/2.38  tff(c_40, plain, (![A_28, B_30]: (v1_tops_1(k3_subset_1(u1_struct_0(A_28), B_30), A_28) | ~v2_tops_1(B_30, A_28) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.83/2.38  tff(c_4928, plain, (![A_28]: (v1_tops_1(u1_struct_0(A_28), A_28) | ~v2_tops_1(k1_xboole_0, A_28) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(superposition, [status(thm), theory('equality')], [c_4895, c_40])).
% 6.83/2.38  tff(c_5425, plain, (![A_355]: (v1_tops_1(u1_struct_0(A_355), A_355) | ~v2_tops_1(k1_xboole_0, A_355) | ~l1_pre_topc(A_355))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4928])).
% 6.83/2.38  tff(c_2703, plain, (![A_250, B_251]: (k2_pre_topc(A_250, B_251)=k2_struct_0(A_250) | ~v1_tops_1(B_251, A_250) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.83/2.38  tff(c_2786, plain, (![A_250]: (k2_pre_topc(A_250, u1_struct_0(A_250))=k2_struct_0(A_250) | ~v1_tops_1(u1_struct_0(A_250), A_250) | ~l1_pre_topc(A_250))), inference(resolution, [status(thm)], [c_70, c_2703])).
% 6.83/2.38  tff(c_5429, plain, (![A_355]: (k2_pre_topc(A_355, u1_struct_0(A_355))=k2_struct_0(A_355) | ~v2_tops_1(k1_xboole_0, A_355) | ~l1_pre_topc(A_355))), inference(resolution, [status(thm)], [c_5425, c_2786])).
% 6.83/2.38  tff(c_5845, plain, (![A_389]: (u1_struct_0(A_389)=k2_struct_0(A_389) | ~v2_tops_1(k1_xboole_0, A_389) | ~l1_pre_topc(A_389) | ~v3_pre_topc(k1_xboole_0, A_389) | ~l1_pre_topc(A_389))), inference(superposition, [status(thm), theory('equality')], [c_5655, c_5429])).
% 6.83/2.38  tff(c_5851, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3') | ~v2_tops_1(k1_xboole_0, '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_823, c_5845])).
% 6.83/2.38  tff(c_5855, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3') | ~v2_tops_1(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5851])).
% 6.83/2.38  tff(c_5856, plain, (~v2_tops_1(k1_xboole_0, '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_5844, c_5855])).
% 6.83/2.38  tff(c_5903, plain, (k1_tops_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_971, c_5856])).
% 6.83/2.38  tff(c_5907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_2458, c_5903])).
% 6.83/2.38  tff(c_5909, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5843])).
% 6.83/2.38  tff(c_2280, plain, (![A_222, B_223]: (v1_tops_1(k3_subset_1(u1_struct_0(A_222), B_223), A_222) | ~v2_tops_1(B_223, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.83/2.38  tff(c_183, plain, (k3_subset_1(u1_struct_0('#skF_3'), k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_62, c_173])).
% 6.83/2.38  tff(c_277, plain, (k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | ~r1_tarski('#skF_4', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_183, c_274])).
% 6.83/2.38  tff(c_483, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_277])).
% 6.83/2.38  tff(c_486, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_483])).
% 6.83/2.38  tff(c_490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_486])).
% 6.83/2.38  tff(c_492, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_277])).
% 6.83/2.38  tff(c_1117, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_492, c_1110])).
% 6.83/2.38  tff(c_1164, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1117])).
% 6.83/2.38  tff(c_1180, plain, (k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1164])).
% 6.83/2.38  tff(c_1447, plain, (![A_179, B_180]: (k2_pre_topc(A_179, B_180)=k2_struct_0(A_179) | ~v1_tops_1(B_180, A_179) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.83/2.38  tff(c_1462, plain, (k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))=k2_struct_0('#skF_3') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_492, c_1447])).
% 6.83/2.38  tff(c_1511, plain, (k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))=k2_struct_0('#skF_3') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1462])).
% 6.83/2.38  tff(c_1512, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1180, c_1511])).
% 6.83/2.38  tff(c_2286, plain, (~v2_tops_1('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2280, c_1512])).
% 6.83/2.38  tff(c_2318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_478, c_2286])).
% 6.83/2.38  tff(c_2320, plain, (k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1164])).
% 6.83/2.38  tff(c_538, plain, (k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_3'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_492, c_535])).
% 6.83/2.38  tff(c_584, plain, (k2_pre_topc('#skF_3', k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_3'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_538])).
% 6.83/2.38  tff(c_3065, plain, (k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2320, c_584])).
% 6.83/2.38  tff(c_3066, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3065])).
% 6.83/2.38  tff(c_60, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.83/2.38  tff(c_3968, plain, (![B_305, A_306]: (v4_pre_topc(B_305, A_306) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_306), B_305), A_306) | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0(A_306))) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.83/2.38  tff(c_3998, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_3968])).
% 6.83/2.38  tff(c_4005, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_492, c_60, c_3998])).
% 6.83/2.38  tff(c_4007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3066, c_4005])).
% 6.83/2.38  tff(c_4008, plain, (k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_3065])).
% 6.83/2.38  tff(c_4025, plain, (k3_subset_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4008, c_183])).
% 6.83/2.38  tff(c_5923, plain, (k3_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5909, c_4025])).
% 6.83/2.38  tff(c_4893, plain, (![A_18]: (k3_subset_1(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4889, c_184])).
% 6.83/2.38  tff(c_6214, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5923, c_4893])).
% 6.83/2.38  tff(c_6238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_6214])).
% 6.83/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.38  
% 6.83/2.38  Inference rules
% 6.83/2.38  ----------------------
% 6.83/2.38  #Ref     : 0
% 6.83/2.38  #Sup     : 1292
% 6.83/2.38  #Fact    : 0
% 6.83/2.38  #Define  : 0
% 6.83/2.38  #Split   : 17
% 6.83/2.38  #Chain   : 0
% 6.83/2.38  #Close   : 0
% 6.83/2.38  
% 6.83/2.38  Ordering : KBO
% 6.83/2.38  
% 6.83/2.38  Simplification rules
% 6.83/2.38  ----------------------
% 6.83/2.38  #Subsume      : 187
% 6.83/2.38  #Demod        : 730
% 6.83/2.38  #Tautology    : 367
% 6.83/2.38  #SimpNegUnit  : 59
% 6.83/2.38  #BackRed      : 89
% 6.83/2.38  
% 6.83/2.38  #Partial instantiations: 0
% 6.83/2.38  #Strategies tried      : 1
% 6.83/2.38  
% 6.83/2.38  Timing (in seconds)
% 6.83/2.38  ----------------------
% 6.83/2.38  Preprocessing        : 0.33
% 6.83/2.38  Parsing              : 0.16
% 6.83/2.38  CNF conversion       : 0.02
% 6.83/2.38  Main loop            : 1.21
% 6.83/2.38  Inferencing          : 0.41
% 6.83/2.38  Reduction            : 0.37
% 6.83/2.38  Demodulation         : 0.25
% 6.83/2.38  BG Simplification    : 0.06
% 6.83/2.38  Subsumption          : 0.26
% 6.83/2.38  Abstraction          : 0.06
% 6.83/2.38  MUC search           : 0.00
% 6.83/2.38  Cooper               : 0.00
% 6.83/2.38  Total                : 1.58
% 6.83/2.38  Index Insertion      : 0.00
% 6.83/2.38  Index Deletion       : 0.00
% 6.83/2.38  Index Matching       : 0.00
% 6.83/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
