%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:25 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 468 expanded)
%              Number of leaves         :   27 ( 172 expanded)
%              Depth                    :   13
%              Number of atoms          :  380 (2036 expanded)
%              Number of equality atoms :   39 (  92 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_72,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_105,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1613,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_53,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1284,plain,(
    ! [B_164,A_165] :
      ( r1_tarski(B_164,k2_pre_topc(A_165,B_164))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1288,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1284])).

tff(c_1294,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1288])).

tff(c_673,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,k2_pre_topc(A_112,B_111))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_677,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_673])).

tff(c_683,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_677])).

tff(c_44,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_64,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_54,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_104,plain,(
    ! [A_60,B_61] :
      ( k1_tops_1(A_60,k2_pre_topc(A_60,B_61)) = B_61
      | ~ v6_tops_1(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_108,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_114,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_108])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_56,B_57] :
      ( v3_pre_topc(k1_tops_1(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_127,plain,(
    ! [A_62,B_63] :
      ( v3_pre_topc(k1_tops_1(A_62,k2_pre_topc(A_62,B_63)),A_62)
      | ~ v2_pre_topc(A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_130,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_127])).

tff(c_132,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_130])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_132])).

tff(c_136,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_135,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_137,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(B_64,k2_pre_topc(A_65,B_64))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_144,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_142])).

tff(c_149,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_144])).

tff(c_180,plain,(
    ! [A_70,B_71] :
      ( k1_tops_1(A_70,k2_pre_topc(A_70,B_71)) = B_71
      | ~ v6_tops_1(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_184,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_180])).

tff(c_190,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_184])).

tff(c_232,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_tarski(k1_tops_1(A_82,B_83),k1_tops_1(A_82,C_84))
      | ~ r1_tarski(B_83,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_240,plain,(
    ! [B_83] :
      ( r1_tarski(k1_tops_1('#skF_1',B_83),'#skF_3')
      | ~ r1_tarski(B_83,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_232])).

tff(c_245,plain,(
    ! [B_83] :
      ( r1_tarski(k1_tops_1('#skF_1',B_83),'#skF_3')
      | ~ r1_tarski(B_83,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_240])).

tff(c_262,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_265,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_262])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_265])).

tff(c_271,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_28,plain,(
    ! [B_31,D_37,C_35,A_23] :
      ( k1_tops_1(B_31,D_37) = D_37
      | ~ v3_pre_topc(D_37,B_31)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0(B_31)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(B_31)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_376,plain,(
    ! [C_93,A_94] :
      ( ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_379,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_271,c_376])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_379])).

tff(c_427,plain,(
    ! [B_96,D_97] :
      ( k1_tops_1(B_96,D_97) = D_97
      | ~ v3_pre_topc(D_97,B_96)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(u1_struct_0(B_96)))
      | ~ l1_pre_topc(B_96) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_436,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_427])).

tff(c_447,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_136,c_436])).

tff(c_328,plain,(
    ! [B_90] :
      ( r1_tarski(k1_tops_1('#skF_1',B_90),'#skF_3')
      | ~ r1_tarski(B_90,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_338,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_328])).

tff(c_347,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_338])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_350,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_347,c_2])).

tff(c_351,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_451,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_351])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_451])).

tff(c_457,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_642,plain,(
    ! [B_109,A_110] :
      ( v4_tops_1(B_109,A_110)
      | ~ r1_tarski(B_109,k2_pre_topc(A_110,k1_tops_1(A_110,B_109)))
      | ~ r1_tarski(k1_tops_1(A_110,k2_pre_topc(A_110,B_109)),B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_656,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_642])).

tff(c_664,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_149,c_457,c_656])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_664])).

tff(c_668,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_670,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_668,c_42])).

tff(c_667,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_794,plain,(
    ! [C_134,A_135] :
      ( ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_800,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_794])).

tff(c_808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_800])).

tff(c_810,plain,(
    ! [B_136,D_137] :
      ( k1_tops_1(B_136,D_137) = D_137
      | ~ v3_pre_topc(D_137,B_136)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0(B_136)))
      | ~ l1_pre_topc(B_136) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_819,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_810])).

tff(c_826,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_667,c_819])).

tff(c_24,plain,(
    ! [A_16,B_20,C_22] :
      ( r1_tarski(k1_tops_1(A_16,B_20),k1_tops_1(A_16,C_22))
      | ~ r1_tarski(B_20,C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_851,plain,(
    ! [C_22] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_22))
      | ~ r1_tarski('#skF_4',C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_24])).

tff(c_895,plain,(
    ! [C_140] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_140))
      | ~ r1_tarski('#skF_4',C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_851])).

tff(c_899,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_895])).

tff(c_905,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_899])).

tff(c_754,plain,(
    ! [A_127,B_128] :
      ( r1_tarski(k1_tops_1(A_127,k2_pre_topc(A_127,B_128)),B_128)
      | ~ v4_tops_1(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1192,plain,(
    ! [A_160,B_161] :
      ( k1_tops_1(A_160,k2_pre_topc(A_160,B_161)) = B_161
      | ~ r1_tarski(B_161,k1_tops_1(A_160,k2_pre_topc(A_160,B_161)))
      | ~ v4_tops_1(B_161,A_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_754,c_2])).

tff(c_1200,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_905,c_1192])).

tff(c_1213,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_683,c_34,c_670,c_1200])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( v6_tops_1(B_13,A_11)
      | k1_tops_1(A_11,k2_pre_topc(A_11,B_13)) != B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1246,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_18])).

tff(c_1269,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1246])).

tff(c_1271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1269])).

tff(c_1273,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1274,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1273,c_48])).

tff(c_1272,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1370,plain,(
    ! [C_187,A_188] :
      ( ~ m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_1376,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1370])).

tff(c_1384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1376])).

tff(c_1387,plain,(
    ! [B_189,D_190] :
      ( k1_tops_1(B_189,D_190) = D_190
      | ~ v3_pre_topc(D_190,B_189)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(u1_struct_0(B_189)))
      | ~ l1_pre_topc(B_189) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1396,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1387])).

tff(c_1403,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1272,c_1396])).

tff(c_1407,plain,(
    ! [C_22] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_22))
      | ~ r1_tarski('#skF_4',C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1403,c_24])).

tff(c_1437,plain,(
    ! [C_193] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_193))
      | ~ r1_tarski('#skF_4',C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1407])).

tff(c_1441,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1437])).

tff(c_1447,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1441])).

tff(c_1346,plain,(
    ! [A_180,B_181] :
      ( r1_tarski(k1_tops_1(A_180,k2_pre_topc(A_180,B_181)),B_181)
      | ~ v4_tops_1(B_181,A_180)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1524,plain,(
    ! [A_205,B_206] :
      ( k1_tops_1(A_205,k2_pre_topc(A_205,B_206)) = B_206
      | ~ r1_tarski(B_206,k1_tops_1(A_205,k2_pre_topc(A_205,B_206)))
      | ~ v4_tops_1(B_206,A_205)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_1346,c_2])).

tff(c_1528,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1447,c_1524])).

tff(c_1535,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1294,c_34,c_1274,c_1528])).

tff(c_1574,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1535,c_18])).

tff(c_1599,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1574])).

tff(c_1601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1599])).

tff(c_1602,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1654,plain,(
    ! [A_216,B_217] :
      ( k1_tops_1(A_216,k2_pre_topc(A_216,B_217)) = B_217
      | ~ v6_tops_1(B_217,A_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1658,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1654])).

tff(c_1664,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1602,c_1658])).

tff(c_1647,plain,(
    ! [A_214,B_215] :
      ( m1_subset_1(k2_pre_topc(A_214,B_215),k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( v3_pre_topc(k1_tops_1(A_14,B_15),A_14)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1687,plain,(
    ! [A_220,B_221] :
      ( v3_pre_topc(k1_tops_1(A_220,k2_pre_topc(A_220,B_221)),A_220)
      | ~ v2_pre_topc(A_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(resolution,[status(thm)],[c_1647,c_22])).

tff(c_1693,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1664,c_1687])).

tff(c_1697,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_1693])).

tff(c_1699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1613,c_1697])).

tff(c_1701,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1700,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1702,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1700])).

tff(c_1708,plain,(
    ! [B_222,A_223] :
      ( r1_tarski(B_222,k2_pre_topc(A_223,B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1710,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1708])).

tff(c_1715,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1710])).

tff(c_1861,plain,(
    ! [C_245,A_246] :
      ( ~ m1_subset_1(C_245,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_1867,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1861])).

tff(c_1875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1867])).

tff(c_1877,plain,(
    ! [B_247,D_248] :
      ( k1_tops_1(B_247,D_248) = D_248
      | ~ v3_pre_topc(D_248,B_247)
      | ~ m1_subset_1(D_248,k1_zfmisc_1(u1_struct_0(B_247)))
      | ~ l1_pre_topc(B_247) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1883,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1877])).

tff(c_1890,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1701,c_1883])).

tff(c_1747,plain,(
    ! [A_230,B_231] :
      ( k1_tops_1(A_230,k2_pre_topc(A_230,B_231)) = B_231
      | ~ v6_tops_1(B_231,A_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1751,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1747])).

tff(c_1757,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1602,c_1751])).

tff(c_2110,plain,(
    ! [B_257,A_258] :
      ( v4_tops_1(B_257,A_258)
      | ~ r1_tarski(B_257,k2_pre_topc(A_258,k1_tops_1(A_258,B_257)))
      | ~ r1_tarski(k1_tops_1(A_258,k2_pre_topc(A_258,B_257)),B_257)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2123,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1757,c_2110])).

tff(c_2129,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_1715,c_1890,c_2123])).

tff(c_2131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1702,c_2129])).

tff(c_2133,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1700])).

tff(c_1603,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_2133,c_1603,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.68  
% 3.85/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.68  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/1.68  
% 3.85/1.68  %Foreground sorts:
% 3.85/1.68  
% 3.85/1.68  
% 3.85/1.68  %Background operators:
% 3.85/1.68  
% 3.85/1.68  
% 3.85/1.68  %Foreground operators:
% 3.85/1.68  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.85/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.68  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 3.85/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.68  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 3.85/1.68  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.85/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/1.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.85/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.68  
% 4.19/1.71  tff(f_131, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 4.19/1.71  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.19/1.71  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 4.19/1.71  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.19/1.71  tff(f_72, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.19/1.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.19/1.71  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 4.19/1.71  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 4.19/1.71  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 4.19/1.71  tff(c_42, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_1613, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.19/1.71  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_46, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_53, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 4.19/1.71  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_1284, plain, (![B_164, A_165]: (r1_tarski(B_164, k2_pre_topc(A_165, B_164)) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.19/1.71  tff(c_1288, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1284])).
% 4.19/1.71  tff(c_1294, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1288])).
% 4.19/1.71  tff(c_673, plain, (![B_111, A_112]: (r1_tarski(B_111, k2_pre_topc(A_112, B_111)) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.19/1.71  tff(c_677, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_673])).
% 4.19/1.71  tff(c_683, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_677])).
% 4.19/1.71  tff(c_44, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_64, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.19/1.71  tff(c_50, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_54, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 4.19/1.71  tff(c_104, plain, (![A_60, B_61]: (k1_tops_1(A_60, k2_pre_topc(A_60, B_61))=B_61 | ~v6_tops_1(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.19/1.71  tff(c_108, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_104])).
% 4.19/1.71  tff(c_114, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_108])).
% 4.19/1.71  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.19/1.71  tff(c_88, plain, (![A_56, B_57]: (v3_pre_topc(k1_tops_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.71  tff(c_127, plain, (![A_62, B_63]: (v3_pre_topc(k1_tops_1(A_62, k2_pre_topc(A_62, B_63)), A_62) | ~v2_pre_topc(A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_8, c_88])).
% 4.19/1.71  tff(c_130, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_114, c_127])).
% 4.19/1.71  tff(c_132, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_130])).
% 4.19/1.71  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_132])).
% 4.19/1.71  tff(c_136, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.19/1.71  tff(c_135, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.19/1.71  tff(c_137, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_135])).
% 4.19/1.71  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.71  tff(c_142, plain, (![B_64, A_65]: (r1_tarski(B_64, k2_pre_topc(A_65, B_64)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.19/1.71  tff(c_144, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_142])).
% 4.19/1.71  tff(c_149, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_144])).
% 4.19/1.71  tff(c_180, plain, (![A_70, B_71]: (k1_tops_1(A_70, k2_pre_topc(A_70, B_71))=B_71 | ~v6_tops_1(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.19/1.71  tff(c_184, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_180])).
% 4.19/1.71  tff(c_190, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_184])).
% 4.19/1.71  tff(c_232, plain, (![A_82, B_83, C_84]: (r1_tarski(k1_tops_1(A_82, B_83), k1_tops_1(A_82, C_84)) | ~r1_tarski(B_83, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.19/1.71  tff(c_240, plain, (![B_83]: (r1_tarski(k1_tops_1('#skF_1', B_83), '#skF_3') | ~r1_tarski(B_83, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_232])).
% 4.19/1.71  tff(c_245, plain, (![B_83]: (r1_tarski(k1_tops_1('#skF_1', B_83), '#skF_3') | ~r1_tarski(B_83, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_240])).
% 4.19/1.71  tff(c_262, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_245])).
% 4.19/1.71  tff(c_265, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_262])).
% 4.19/1.71  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_265])).
% 4.19/1.71  tff(c_271, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_245])).
% 4.19/1.71  tff(c_28, plain, (![B_31, D_37, C_35, A_23]: (k1_tops_1(B_31, D_37)=D_37 | ~v3_pre_topc(D_37, B_31) | ~m1_subset_1(D_37, k1_zfmisc_1(u1_struct_0(B_31))) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(B_31) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.19/1.71  tff(c_376, plain, (![C_93, A_94]: (~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(splitLeft, [status(thm)], [c_28])).
% 4.19/1.71  tff(c_379, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_271, c_376])).
% 4.19/1.71  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_379])).
% 4.19/1.71  tff(c_427, plain, (![B_96, D_97]: (k1_tops_1(B_96, D_97)=D_97 | ~v3_pre_topc(D_97, B_96) | ~m1_subset_1(D_97, k1_zfmisc_1(u1_struct_0(B_96))) | ~l1_pre_topc(B_96))), inference(splitRight, [status(thm)], [c_28])).
% 4.19/1.71  tff(c_436, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_427])).
% 4.19/1.71  tff(c_447, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_136, c_436])).
% 4.19/1.71  tff(c_328, plain, (![B_90]: (r1_tarski(k1_tops_1('#skF_1', B_90), '#skF_3') | ~r1_tarski(B_90, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_245])).
% 4.19/1.71  tff(c_338, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_328])).
% 4.19/1.71  tff(c_347, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_338])).
% 4.19/1.71  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.71  tff(c_350, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_347, c_2])).
% 4.19/1.71  tff(c_351, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_350])).
% 4.19/1.71  tff(c_451, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_447, c_351])).
% 4.19/1.71  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_451])).
% 4.19/1.71  tff(c_457, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_350])).
% 4.19/1.71  tff(c_642, plain, (![B_109, A_110]: (v4_tops_1(B_109, A_110) | ~r1_tarski(B_109, k2_pre_topc(A_110, k1_tops_1(A_110, B_109))) | ~r1_tarski(k1_tops_1(A_110, k2_pre_topc(A_110, B_109)), B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.19/1.71  tff(c_656, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_190, c_642])).
% 4.19/1.71  tff(c_664, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_6, c_149, c_457, c_656])).
% 4.19/1.71  tff(c_666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_664])).
% 4.19/1.71  tff(c_668, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_135])).
% 4.19/1.71  tff(c_670, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_668, c_42])).
% 4.19/1.71  tff(c_667, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_135])).
% 4.19/1.71  tff(c_794, plain, (![C_134, A_135]: (~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(splitLeft, [status(thm)], [c_28])).
% 4.19/1.71  tff(c_800, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_794])).
% 4.19/1.71  tff(c_808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_800])).
% 4.19/1.71  tff(c_810, plain, (![B_136, D_137]: (k1_tops_1(B_136, D_137)=D_137 | ~v3_pre_topc(D_137, B_136) | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0(B_136))) | ~l1_pre_topc(B_136))), inference(splitRight, [status(thm)], [c_28])).
% 4.19/1.71  tff(c_819, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_810])).
% 4.19/1.71  tff(c_826, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_667, c_819])).
% 4.19/1.71  tff(c_24, plain, (![A_16, B_20, C_22]: (r1_tarski(k1_tops_1(A_16, B_20), k1_tops_1(A_16, C_22)) | ~r1_tarski(B_20, C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.19/1.71  tff(c_851, plain, (![C_22]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_22)) | ~r1_tarski('#skF_4', C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_826, c_24])).
% 4.19/1.71  tff(c_895, plain, (![C_140]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_140)) | ~r1_tarski('#skF_4', C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_851])).
% 4.19/1.71  tff(c_899, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_895])).
% 4.19/1.71  tff(c_905, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_899])).
% 4.19/1.71  tff(c_754, plain, (![A_127, B_128]: (r1_tarski(k1_tops_1(A_127, k2_pre_topc(A_127, B_128)), B_128) | ~v4_tops_1(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.19/1.71  tff(c_1192, plain, (![A_160, B_161]: (k1_tops_1(A_160, k2_pre_topc(A_160, B_161))=B_161 | ~r1_tarski(B_161, k1_tops_1(A_160, k2_pre_topc(A_160, B_161))) | ~v4_tops_1(B_161, A_160) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_754, c_2])).
% 4.19/1.71  tff(c_1200, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_905, c_1192])).
% 4.19/1.71  tff(c_1213, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_683, c_34, c_670, c_1200])).
% 4.19/1.71  tff(c_18, plain, (![B_13, A_11]: (v6_tops_1(B_13, A_11) | k1_tops_1(A_11, k2_pre_topc(A_11, B_13))!=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.19/1.71  tff(c_1246, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1213, c_18])).
% 4.19/1.71  tff(c_1269, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1246])).
% 4.19/1.71  tff(c_1271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1269])).
% 4.19/1.71  tff(c_1273, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.19/1.71  tff(c_48, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_1274, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1273, c_48])).
% 4.19/1.71  tff(c_1272, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 4.19/1.71  tff(c_1370, plain, (![C_187, A_188]: (~m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188))), inference(splitLeft, [status(thm)], [c_28])).
% 4.19/1.71  tff(c_1376, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1370])).
% 4.19/1.71  tff(c_1384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1376])).
% 4.19/1.71  tff(c_1387, plain, (![B_189, D_190]: (k1_tops_1(B_189, D_190)=D_190 | ~v3_pre_topc(D_190, B_189) | ~m1_subset_1(D_190, k1_zfmisc_1(u1_struct_0(B_189))) | ~l1_pre_topc(B_189))), inference(splitRight, [status(thm)], [c_28])).
% 4.19/1.71  tff(c_1396, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1387])).
% 4.19/1.71  tff(c_1403, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1272, c_1396])).
% 4.19/1.71  tff(c_1407, plain, (![C_22]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_22)) | ~r1_tarski('#skF_4', C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1403, c_24])).
% 4.19/1.71  tff(c_1437, plain, (![C_193]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_193)) | ~r1_tarski('#skF_4', C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1407])).
% 4.19/1.71  tff(c_1441, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1437])).
% 4.19/1.71  tff(c_1447, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1441])).
% 4.19/1.71  tff(c_1346, plain, (![A_180, B_181]: (r1_tarski(k1_tops_1(A_180, k2_pre_topc(A_180, B_181)), B_181) | ~v4_tops_1(B_181, A_180) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.19/1.71  tff(c_1524, plain, (![A_205, B_206]: (k1_tops_1(A_205, k2_pre_topc(A_205, B_206))=B_206 | ~r1_tarski(B_206, k1_tops_1(A_205, k2_pre_topc(A_205, B_206))) | ~v4_tops_1(B_206, A_205) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(resolution, [status(thm)], [c_1346, c_2])).
% 4.19/1.71  tff(c_1528, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1447, c_1524])).
% 4.19/1.71  tff(c_1535, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1294, c_34, c_1274, c_1528])).
% 4.19/1.71  tff(c_1574, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1535, c_18])).
% 4.19/1.71  tff(c_1599, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1574])).
% 4.19/1.71  tff(c_1601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1599])).
% 4.19/1.71  tff(c_1602, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.19/1.71  tff(c_1654, plain, (![A_216, B_217]: (k1_tops_1(A_216, k2_pre_topc(A_216, B_217))=B_217 | ~v6_tops_1(B_217, A_216) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.19/1.71  tff(c_1658, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1654])).
% 4.19/1.71  tff(c_1664, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1602, c_1658])).
% 4.19/1.71  tff(c_1647, plain, (![A_214, B_215]: (m1_subset_1(k2_pre_topc(A_214, B_215), k1_zfmisc_1(u1_struct_0(A_214))) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.19/1.71  tff(c_22, plain, (![A_14, B_15]: (v3_pre_topc(k1_tops_1(A_14, B_15), A_14) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.19/1.71  tff(c_1687, plain, (![A_220, B_221]: (v3_pre_topc(k1_tops_1(A_220, k2_pre_topc(A_220, B_221)), A_220) | ~v2_pre_topc(A_220) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(resolution, [status(thm)], [c_1647, c_22])).
% 4.19/1.71  tff(c_1693, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1664, c_1687])).
% 4.19/1.71  tff(c_1697, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_1693])).
% 4.19/1.71  tff(c_1699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1613, c_1697])).
% 4.19/1.71  tff(c_1701, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.19/1.71  tff(c_1700, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.19/1.71  tff(c_1702, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1700])).
% 4.19/1.71  tff(c_1708, plain, (![B_222, A_223]: (r1_tarski(B_222, k2_pre_topc(A_223, B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.19/1.71  tff(c_1710, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1708])).
% 4.19/1.71  tff(c_1715, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1710])).
% 4.19/1.71  tff(c_1861, plain, (![C_245, A_246]: (~m1_subset_1(C_245, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246))), inference(splitLeft, [status(thm)], [c_28])).
% 4.19/1.71  tff(c_1867, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1861])).
% 4.19/1.71  tff(c_1875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1867])).
% 4.19/1.71  tff(c_1877, plain, (![B_247, D_248]: (k1_tops_1(B_247, D_248)=D_248 | ~v3_pre_topc(D_248, B_247) | ~m1_subset_1(D_248, k1_zfmisc_1(u1_struct_0(B_247))) | ~l1_pre_topc(B_247))), inference(splitRight, [status(thm)], [c_28])).
% 4.19/1.71  tff(c_1883, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1877])).
% 4.19/1.71  tff(c_1890, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1701, c_1883])).
% 4.19/1.71  tff(c_1747, plain, (![A_230, B_231]: (k1_tops_1(A_230, k2_pre_topc(A_230, B_231))=B_231 | ~v6_tops_1(B_231, A_230) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.19/1.71  tff(c_1751, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1747])).
% 4.19/1.71  tff(c_1757, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1602, c_1751])).
% 4.19/1.71  tff(c_2110, plain, (![B_257, A_258]: (v4_tops_1(B_257, A_258) | ~r1_tarski(B_257, k2_pre_topc(A_258, k1_tops_1(A_258, B_257))) | ~r1_tarski(k1_tops_1(A_258, k2_pre_topc(A_258, B_257)), B_257) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.19/1.71  tff(c_2123, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1757, c_2110])).
% 4.19/1.71  tff(c_2129, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_6, c_1715, c_1890, c_2123])).
% 4.19/1.71  tff(c_2131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1702, c_2129])).
% 4.19/1.71  tff(c_2133, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1700])).
% 4.19/1.71  tff(c_1603, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.19/1.71  tff(c_40, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.19/1.71  tff(c_2135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1701, c_2133, c_1603, c_40])).
% 4.19/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.71  
% 4.19/1.71  Inference rules
% 4.19/1.71  ----------------------
% 4.19/1.71  #Ref     : 0
% 4.19/1.71  #Sup     : 386
% 4.19/1.71  #Fact    : 0
% 4.19/1.71  #Define  : 0
% 4.19/1.71  #Split   : 63
% 4.19/1.71  #Chain   : 0
% 4.19/1.71  #Close   : 0
% 4.19/1.71  
% 4.19/1.71  Ordering : KBO
% 4.19/1.71  
% 4.19/1.71  Simplification rules
% 4.19/1.71  ----------------------
% 4.19/1.71  #Subsume      : 115
% 4.19/1.71  #Demod        : 598
% 4.19/1.71  #Tautology    : 117
% 4.19/1.71  #SimpNegUnit  : 16
% 4.19/1.71  #BackRed      : 7
% 4.19/1.71  
% 4.19/1.71  #Partial instantiations: 0
% 4.19/1.71  #Strategies tried      : 1
% 4.19/1.71  
% 4.19/1.71  Timing (in seconds)
% 4.19/1.71  ----------------------
% 4.19/1.71  Preprocessing        : 0.31
% 4.19/1.71  Parsing              : 0.17
% 4.19/1.71  CNF conversion       : 0.02
% 4.19/1.71  Main loop            : 0.60
% 4.19/1.71  Inferencing          : 0.21
% 4.19/1.71  Reduction            : 0.20
% 4.19/1.71  Demodulation         : 0.14
% 4.19/1.71  BG Simplification    : 0.02
% 4.19/1.71  Subsumption          : 0.12
% 4.19/1.71  Abstraction          : 0.03
% 4.19/1.71  MUC search           : 0.00
% 4.19/1.71  Cooper               : 0.00
% 4.19/1.71  Total                : 0.98
% 4.19/1.71  Index Insertion      : 0.00
% 4.19/1.71  Index Deletion       : 0.00
% 4.19/1.71  Index Matching       : 0.00
% 4.19/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
