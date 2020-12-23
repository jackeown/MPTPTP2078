%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:25 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 390 expanded)
%              Number of leaves         :   27 ( 145 expanded)
%              Depth                    :    9
%              Number of atoms          :  370 (1645 expanded)
%              Number of equality atoms :   37 (  72 expanded)
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

tff(f_133,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_93,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(c_44,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1516,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_53,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_64,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

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

tff(c_136,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_26,plain,(
    ! [B_24,D_30,C_28,A_16] :
      ( k1_tops_1(B_24,D_30) = D_30
      | ~ v3_pre_topc(D_30,B_24)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0(B_24)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_280,plain,(
    ! [C_88,A_89] :
      ( ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_286,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_280])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_286])).

tff(c_312,plain,(
    ! [B_91,D_92] :
      ( k1_tops_1(B_91,D_92) = D_92
      | ~ v3_pre_topc(D_92,B_91)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(u1_struct_0(B_91)))
      | ~ l1_pre_topc(B_91) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_318,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_312])).

tff(c_325,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_136,c_318])).

tff(c_248,plain,(
    ! [B_84,A_85,C_86] :
      ( r1_tarski(B_84,k1_tops_1(A_85,C_86))
      | ~ r1_tarski(B_84,C_86)
      | ~ v3_pre_topc(B_84,A_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_252,plain,(
    ! [B_84] :
      ( r1_tarski(B_84,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_84,'#skF_3')
      | ~ v3_pre_topc(B_84,'#skF_1')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_248])).

tff(c_262,plain,(
    ! [B_87] :
      ( r1_tarski(B_87,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_87,'#skF_3')
      | ~ v3_pre_topc(B_87,'#skF_1')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_252])).

tff(c_269,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_262])).

tff(c_275,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_6,c_269])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_278,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_275,c_2])).

tff(c_296,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_329,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_296])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_329])).

tff(c_336,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_278])).

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

tff(c_470,plain,(
    ! [B_110,A_111] :
      ( v4_tops_1(B_110,A_111)
      | ~ r1_tarski(B_110,k2_pre_topc(A_111,k1_tops_1(A_111,B_110)))
      | ~ r1_tarski(k1_tops_1(A_111,k2_pre_topc(A_111,B_110)),B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_476,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_470])).

tff(c_479,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_149,c_336,c_476])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_479])).

tff(c_482,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_483,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_485,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_483,c_42])).

tff(c_488,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(B_112,k2_pre_topc(A_113,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_492,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_488])).

tff(c_498,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_492])).

tff(c_594,plain,(
    ! [B_132,A_133,C_134] :
      ( r1_tarski(B_132,k1_tops_1(A_133,C_134))
      | ~ r1_tarski(B_132,C_134)
      | ~ v3_pre_topc(B_132,A_133)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_976,plain,(
    ! [B_177,A_178,B_179] :
      ( r1_tarski(B_177,k1_tops_1(A_178,k2_pre_topc(A_178,B_179)))
      | ~ r1_tarski(B_177,k2_pre_topc(A_178,B_179))
      | ~ v3_pre_topc(B_177,A_178)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_8,c_594])).

tff(c_569,plain,(
    ! [A_128,B_129] :
      ( r1_tarski(k1_tops_1(A_128,k2_pre_topc(A_128,B_129)),B_129)
      | ~ v4_tops_1(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_575,plain,(
    ! [A_128,B_129] :
      ( k1_tops_1(A_128,k2_pre_topc(A_128,B_129)) = B_129
      | ~ r1_tarski(B_129,k1_tops_1(A_128,k2_pre_topc(A_128,B_129)))
      | ~ v4_tops_1(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_569,c_2])).

tff(c_1064,plain,(
    ! [A_184,B_185] :
      ( k1_tops_1(A_184,k2_pre_topc(A_184,B_185)) = B_185
      | ~ v4_tops_1(B_185,A_184)
      | ~ r1_tarski(B_185,k2_pre_topc(A_184,B_185))
      | ~ v3_pre_topc(B_185,A_184)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_976,c_575])).

tff(c_1068,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_498,c_1064])).

tff(c_1074,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_482,c_485,c_1068])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( v6_tops_1(B_13,A_11)
      | k1_tops_1(A_11,k2_pre_topc(A_11,B_13)) != B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1101,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_18])).

tff(c_1120,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1101])).

tff(c_1122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1120])).

tff(c_1123,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1124,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1125,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1124,c_48])).

tff(c_1135,plain,(
    ! [B_188,A_189] :
      ( r1_tarski(B_188,k2_pre_topc(A_189,B_188))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1139,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1135])).

tff(c_1145,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1139])).

tff(c_1247,plain,(
    ! [B_212,A_213,C_214] :
      ( r1_tarski(B_212,k1_tops_1(A_213,C_214))
      | ~ r1_tarski(B_212,C_214)
      | ~ v3_pre_topc(B_212,A_213)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1427,plain,(
    ! [B_238,A_239,B_240] :
      ( r1_tarski(B_238,k1_tops_1(A_239,k2_pre_topc(A_239,B_240)))
      | ~ r1_tarski(B_238,k2_pre_topc(A_239,B_240))
      | ~ v3_pre_topc(B_238,A_239)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(resolution,[status(thm)],[c_8,c_1247])).

tff(c_1197,plain,(
    ! [A_204,B_205] :
      ( r1_tarski(k1_tops_1(A_204,k2_pre_topc(A_204,B_205)),B_205)
      | ~ v4_tops_1(B_205,A_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1200,plain,(
    ! [A_204,B_205] :
      ( k1_tops_1(A_204,k2_pre_topc(A_204,B_205)) = B_205
      | ~ r1_tarski(B_205,k1_tops_1(A_204,k2_pre_topc(A_204,B_205)))
      | ~ v4_tops_1(B_205,A_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(resolution,[status(thm)],[c_1197,c_2])).

tff(c_1446,plain,(
    ! [A_241,B_242] :
      ( k1_tops_1(A_241,k2_pre_topc(A_241,B_242)) = B_242
      | ~ v4_tops_1(B_242,A_241)
      | ~ r1_tarski(B_242,k2_pre_topc(A_241,B_242))
      | ~ v3_pre_topc(B_242,A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_1427,c_1200])).

tff(c_1450,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1145,c_1446])).

tff(c_1456,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1123,c_1125,c_1450])).

tff(c_1483,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_18])).

tff(c_1502,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1483])).

tff(c_1504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1502])).

tff(c_1505,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1556,plain,(
    ! [A_251,B_252] :
      ( k1_tops_1(A_251,k2_pre_topc(A_251,B_252)) = B_252
      | ~ v6_tops_1(B_252,A_251)
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1560,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1556])).

tff(c_1566,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1505,c_1560])).

tff(c_1542,plain,(
    ! [A_249,B_250] :
      ( v3_pre_topc(k1_tops_1(A_249,B_250),A_249)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1590,plain,(
    ! [A_255,B_256] :
      ( v3_pre_topc(k1_tops_1(A_255,k2_pre_topc(A_255,B_256)),A_255)
      | ~ v2_pre_topc(A_255)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(resolution,[status(thm)],[c_8,c_1542])).

tff(c_1596,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1566,c_1590])).

tff(c_1600,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_1596])).

tff(c_1602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1516,c_1600])).

tff(c_1604,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1603,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1605,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1603])).

tff(c_1610,plain,(
    ! [B_257,A_258] :
      ( r1_tarski(B_257,k2_pre_topc(A_258,B_257))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1612,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1610])).

tff(c_1617,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1612])).

tff(c_1833,plain,(
    ! [C_288,A_289] :
      ( ~ m1_subset_1(C_288,k1_zfmisc_1(u1_struct_0(A_289)))
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_1839,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1833])).

tff(c_1847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1839])).

tff(c_1850,plain,(
    ! [B_290,D_291] :
      ( k1_tops_1(B_290,D_291) = D_291
      | ~ v3_pre_topc(D_291,B_290)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(u1_struct_0(B_290)))
      | ~ l1_pre_topc(B_290) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1856,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1850])).

tff(c_1863,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1604,c_1856])).

tff(c_1785,plain,(
    ! [B_283,A_284,C_285] :
      ( r1_tarski(B_283,k1_tops_1(A_284,C_285))
      | ~ r1_tarski(B_283,C_285)
      | ~ v3_pre_topc(B_283,A_284)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1789,plain,(
    ! [B_283] :
      ( r1_tarski(B_283,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_283,'#skF_3')
      | ~ v3_pre_topc(B_283,'#skF_1')
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_1785])).

tff(c_1799,plain,(
    ! [B_286] :
      ( r1_tarski(B_286,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_286,'#skF_3')
      | ~ v3_pre_topc(B_286,'#skF_1')
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1789])).

tff(c_1806,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1799])).

tff(c_1812,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_6,c_1806])).

tff(c_1815,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1812,c_2])).

tff(c_1816,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1815])).

tff(c_1867,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1816])).

tff(c_1873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1867])).

tff(c_1874,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1815])).

tff(c_1648,plain,(
    ! [A_263,B_264] :
      ( k1_tops_1(A_263,k2_pre_topc(A_263,B_264)) = B_264
      | ~ v6_tops_1(B_264,A_263)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1652,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1648])).

tff(c_1658,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1505,c_1652])).

tff(c_1946,plain,(
    ! [B_300,A_301] :
      ( v4_tops_1(B_300,A_301)
      | ~ r1_tarski(B_300,k2_pre_topc(A_301,k1_tops_1(A_301,B_300)))
      | ~ r1_tarski(k1_tops_1(A_301,k2_pre_topc(A_301,B_300)),B_300)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1955,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1658,c_1946])).

tff(c_1960,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_1617,c_1874,c_1955])).

tff(c_1962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1605,c_1960])).

tff(c_1964,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1603])).

tff(c_1506,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_1964,c_1506,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.76  
% 3.99/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.76  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.99/1.76  
% 3.99/1.76  %Foreground sorts:
% 3.99/1.76  
% 3.99/1.76  
% 3.99/1.76  %Background operators:
% 3.99/1.76  
% 3.99/1.76  
% 3.99/1.76  %Foreground operators:
% 3.99/1.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.99/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.76  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 3.99/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.99/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.76  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 3.99/1.76  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.99/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.99/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.99/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.76  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.99/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.99/1.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.99/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.76  
% 4.41/1.79  tff(f_133, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 4.41/1.79  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 4.41/1.79  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.41/1.79  tff(f_72, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.41/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.41/1.79  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.41/1.79  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 4.41/1.79  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 4.41/1.79  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 4.41/1.79  tff(c_44, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_1516, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.41/1.79  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_46, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_53, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 4.41/1.79  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_64, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.41/1.79  tff(c_50, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_54, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 4.41/1.79  tff(c_104, plain, (![A_60, B_61]: (k1_tops_1(A_60, k2_pre_topc(A_60, B_61))=B_61 | ~v6_tops_1(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.41/1.79  tff(c_108, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_104])).
% 4.41/1.79  tff(c_114, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_108])).
% 4.41/1.79  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.41/1.79  tff(c_88, plain, (![A_56, B_57]: (v3_pre_topc(k1_tops_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.41/1.79  tff(c_127, plain, (![A_62, B_63]: (v3_pre_topc(k1_tops_1(A_62, k2_pre_topc(A_62, B_63)), A_62) | ~v2_pre_topc(A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_8, c_88])).
% 4.41/1.79  tff(c_130, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_114, c_127])).
% 4.41/1.79  tff(c_132, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_130])).
% 4.41/1.79  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_132])).
% 4.41/1.79  tff(c_135, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.41/1.79  tff(c_137, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_135])).
% 4.41/1.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.79  tff(c_142, plain, (![B_64, A_65]: (r1_tarski(B_64, k2_pre_topc(A_65, B_64)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.41/1.79  tff(c_144, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_142])).
% 4.41/1.79  tff(c_149, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_144])).
% 4.41/1.79  tff(c_136, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.41/1.79  tff(c_26, plain, (![B_24, D_30, C_28, A_16]: (k1_tops_1(B_24, D_30)=D_30 | ~v3_pre_topc(D_30, B_24) | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0(B_24))) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(B_24) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.41/1.79  tff(c_280, plain, (![C_88, A_89]: (~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(splitLeft, [status(thm)], [c_26])).
% 4.41/1.79  tff(c_286, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_280])).
% 4.41/1.79  tff(c_294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_286])).
% 4.41/1.79  tff(c_312, plain, (![B_91, D_92]: (k1_tops_1(B_91, D_92)=D_92 | ~v3_pre_topc(D_92, B_91) | ~m1_subset_1(D_92, k1_zfmisc_1(u1_struct_0(B_91))) | ~l1_pre_topc(B_91))), inference(splitRight, [status(thm)], [c_26])).
% 4.41/1.79  tff(c_318, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_312])).
% 4.41/1.79  tff(c_325, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_136, c_318])).
% 4.41/1.79  tff(c_248, plain, (![B_84, A_85, C_86]: (r1_tarski(B_84, k1_tops_1(A_85, C_86)) | ~r1_tarski(B_84, C_86) | ~v3_pre_topc(B_84, A_85) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.41/1.79  tff(c_252, plain, (![B_84]: (r1_tarski(B_84, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_84, '#skF_3') | ~v3_pre_topc(B_84, '#skF_1') | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_248])).
% 4.41/1.79  tff(c_262, plain, (![B_87]: (r1_tarski(B_87, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_87, '#skF_3') | ~v3_pre_topc(B_87, '#skF_1') | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_252])).
% 4.41/1.79  tff(c_269, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_262])).
% 4.41/1.79  tff(c_275, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_6, c_269])).
% 4.41/1.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.79  tff(c_278, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_275, c_2])).
% 4.41/1.79  tff(c_296, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_278])).
% 4.41/1.79  tff(c_329, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_296])).
% 4.41/1.79  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_329])).
% 4.41/1.79  tff(c_336, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_278])).
% 4.41/1.79  tff(c_180, plain, (![A_70, B_71]: (k1_tops_1(A_70, k2_pre_topc(A_70, B_71))=B_71 | ~v6_tops_1(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.41/1.79  tff(c_184, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_180])).
% 4.41/1.79  tff(c_190, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_184])).
% 4.41/1.79  tff(c_470, plain, (![B_110, A_111]: (v4_tops_1(B_110, A_111) | ~r1_tarski(B_110, k2_pre_topc(A_111, k1_tops_1(A_111, B_110))) | ~r1_tarski(k1_tops_1(A_111, k2_pre_topc(A_111, B_110)), B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.41/1.79  tff(c_476, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_190, c_470])).
% 4.41/1.79  tff(c_479, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_6, c_149, c_336, c_476])).
% 4.41/1.79  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_479])).
% 4.41/1.79  tff(c_482, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_135])).
% 4.41/1.79  tff(c_483, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_135])).
% 4.41/1.79  tff(c_42, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_485, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_483, c_42])).
% 4.41/1.79  tff(c_488, plain, (![B_112, A_113]: (r1_tarski(B_112, k2_pre_topc(A_113, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.41/1.79  tff(c_492, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_488])).
% 4.41/1.79  tff(c_498, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_492])).
% 4.41/1.79  tff(c_594, plain, (![B_132, A_133, C_134]: (r1_tarski(B_132, k1_tops_1(A_133, C_134)) | ~r1_tarski(B_132, C_134) | ~v3_pre_topc(B_132, A_133) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.41/1.79  tff(c_976, plain, (![B_177, A_178, B_179]: (r1_tarski(B_177, k1_tops_1(A_178, k2_pre_topc(A_178, B_179))) | ~r1_tarski(B_177, k2_pre_topc(A_178, B_179)) | ~v3_pre_topc(B_177, A_178) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_178))) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(resolution, [status(thm)], [c_8, c_594])).
% 4.41/1.79  tff(c_569, plain, (![A_128, B_129]: (r1_tarski(k1_tops_1(A_128, k2_pre_topc(A_128, B_129)), B_129) | ~v4_tops_1(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.41/1.79  tff(c_575, plain, (![A_128, B_129]: (k1_tops_1(A_128, k2_pre_topc(A_128, B_129))=B_129 | ~r1_tarski(B_129, k1_tops_1(A_128, k2_pre_topc(A_128, B_129))) | ~v4_tops_1(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_569, c_2])).
% 4.41/1.79  tff(c_1064, plain, (![A_184, B_185]: (k1_tops_1(A_184, k2_pre_topc(A_184, B_185))=B_185 | ~v4_tops_1(B_185, A_184) | ~r1_tarski(B_185, k2_pre_topc(A_184, B_185)) | ~v3_pre_topc(B_185, A_184) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_976, c_575])).
% 4.41/1.79  tff(c_1068, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_498, c_1064])).
% 4.41/1.79  tff(c_1074, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_482, c_485, c_1068])).
% 4.41/1.79  tff(c_18, plain, (![B_13, A_11]: (v6_tops_1(B_13, A_11) | k1_tops_1(A_11, k2_pre_topc(A_11, B_13))!=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.41/1.79  tff(c_1101, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1074, c_18])).
% 4.41/1.79  tff(c_1120, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1101])).
% 4.41/1.79  tff(c_1122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1120])).
% 4.41/1.79  tff(c_1123, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 4.41/1.79  tff(c_1124, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.41/1.79  tff(c_48, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_1125, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1124, c_48])).
% 4.41/1.79  tff(c_1135, plain, (![B_188, A_189]: (r1_tarski(B_188, k2_pre_topc(A_189, B_188)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.41/1.79  tff(c_1139, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1135])).
% 4.41/1.79  tff(c_1145, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1139])).
% 4.41/1.79  tff(c_1247, plain, (![B_212, A_213, C_214]: (r1_tarski(B_212, k1_tops_1(A_213, C_214)) | ~r1_tarski(B_212, C_214) | ~v3_pre_topc(B_212, A_213) | ~m1_subset_1(C_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.41/1.79  tff(c_1427, plain, (![B_238, A_239, B_240]: (r1_tarski(B_238, k1_tops_1(A_239, k2_pre_topc(A_239, B_240))) | ~r1_tarski(B_238, k2_pre_topc(A_239, B_240)) | ~v3_pre_topc(B_238, A_239) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0(A_239))) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(resolution, [status(thm)], [c_8, c_1247])).
% 4.41/1.79  tff(c_1197, plain, (![A_204, B_205]: (r1_tarski(k1_tops_1(A_204, k2_pre_topc(A_204, B_205)), B_205) | ~v4_tops_1(B_205, A_204) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.41/1.79  tff(c_1200, plain, (![A_204, B_205]: (k1_tops_1(A_204, k2_pre_topc(A_204, B_205))=B_205 | ~r1_tarski(B_205, k1_tops_1(A_204, k2_pre_topc(A_204, B_205))) | ~v4_tops_1(B_205, A_204) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204))), inference(resolution, [status(thm)], [c_1197, c_2])).
% 4.41/1.79  tff(c_1446, plain, (![A_241, B_242]: (k1_tops_1(A_241, k2_pre_topc(A_241, B_242))=B_242 | ~v4_tops_1(B_242, A_241) | ~r1_tarski(B_242, k2_pre_topc(A_241, B_242)) | ~v3_pre_topc(B_242, A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_1427, c_1200])).
% 4.41/1.79  tff(c_1450, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1145, c_1446])).
% 4.41/1.79  tff(c_1456, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1123, c_1125, c_1450])).
% 4.41/1.79  tff(c_1483, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1456, c_18])).
% 4.41/1.79  tff(c_1502, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1483])).
% 4.41/1.79  tff(c_1504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1502])).
% 4.41/1.79  tff(c_1505, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.41/1.79  tff(c_1556, plain, (![A_251, B_252]: (k1_tops_1(A_251, k2_pre_topc(A_251, B_252))=B_252 | ~v6_tops_1(B_252, A_251) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.41/1.79  tff(c_1560, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1556])).
% 4.41/1.79  tff(c_1566, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1505, c_1560])).
% 4.41/1.79  tff(c_1542, plain, (![A_249, B_250]: (v3_pre_topc(k1_tops_1(A_249, B_250), A_249) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.41/1.79  tff(c_1590, plain, (![A_255, B_256]: (v3_pre_topc(k1_tops_1(A_255, k2_pre_topc(A_255, B_256)), A_255) | ~v2_pre_topc(A_255) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(resolution, [status(thm)], [c_8, c_1542])).
% 4.41/1.79  tff(c_1596, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1566, c_1590])).
% 4.41/1.79  tff(c_1600, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_1596])).
% 4.41/1.79  tff(c_1602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1516, c_1600])).
% 4.41/1.79  tff(c_1604, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.41/1.79  tff(c_1603, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.41/1.79  tff(c_1605, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1603])).
% 4.41/1.79  tff(c_1610, plain, (![B_257, A_258]: (r1_tarski(B_257, k2_pre_topc(A_258, B_257)) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.41/1.79  tff(c_1612, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1610])).
% 4.41/1.79  tff(c_1617, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1612])).
% 4.41/1.79  tff(c_1833, plain, (![C_288, A_289]: (~m1_subset_1(C_288, k1_zfmisc_1(u1_struct_0(A_289))) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289))), inference(splitLeft, [status(thm)], [c_26])).
% 4.41/1.79  tff(c_1839, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1833])).
% 4.41/1.79  tff(c_1847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1839])).
% 4.41/1.79  tff(c_1850, plain, (![B_290, D_291]: (k1_tops_1(B_290, D_291)=D_291 | ~v3_pre_topc(D_291, B_290) | ~m1_subset_1(D_291, k1_zfmisc_1(u1_struct_0(B_290))) | ~l1_pre_topc(B_290))), inference(splitRight, [status(thm)], [c_26])).
% 4.41/1.79  tff(c_1856, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1850])).
% 4.41/1.79  tff(c_1863, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1604, c_1856])).
% 4.41/1.79  tff(c_1785, plain, (![B_283, A_284, C_285]: (r1_tarski(B_283, k1_tops_1(A_284, C_285)) | ~r1_tarski(B_283, C_285) | ~v3_pre_topc(B_283, A_284) | ~m1_subset_1(C_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.41/1.79  tff(c_1789, plain, (![B_283]: (r1_tarski(B_283, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_283, '#skF_3') | ~v3_pre_topc(B_283, '#skF_1') | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_1785])).
% 4.41/1.79  tff(c_1799, plain, (![B_286]: (r1_tarski(B_286, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_286, '#skF_3') | ~v3_pre_topc(B_286, '#skF_1') | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1789])).
% 4.41/1.79  tff(c_1806, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_1799])).
% 4.41/1.79  tff(c_1812, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1604, c_6, c_1806])).
% 4.41/1.79  tff(c_1815, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1812, c_2])).
% 4.41/1.79  tff(c_1816, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1815])).
% 4.41/1.79  tff(c_1867, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1816])).
% 4.41/1.79  tff(c_1873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1867])).
% 4.41/1.79  tff(c_1874, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1815])).
% 4.41/1.79  tff(c_1648, plain, (![A_263, B_264]: (k1_tops_1(A_263, k2_pre_topc(A_263, B_264))=B_264 | ~v6_tops_1(B_264, A_263) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.41/1.79  tff(c_1652, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1648])).
% 4.41/1.79  tff(c_1658, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1505, c_1652])).
% 4.41/1.79  tff(c_1946, plain, (![B_300, A_301]: (v4_tops_1(B_300, A_301) | ~r1_tarski(B_300, k2_pre_topc(A_301, k1_tops_1(A_301, B_300))) | ~r1_tarski(k1_tops_1(A_301, k2_pre_topc(A_301, B_300)), B_300) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.41/1.79  tff(c_1955, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1658, c_1946])).
% 4.41/1.79  tff(c_1960, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_6, c_1617, c_1874, c_1955])).
% 4.41/1.79  tff(c_1962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1605, c_1960])).
% 4.41/1.79  tff(c_1964, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1603])).
% 4.41/1.79  tff(c_1506, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.41/1.79  tff(c_40, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.41/1.79  tff(c_1968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1604, c_1964, c_1506, c_40])).
% 4.41/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.79  
% 4.41/1.79  Inference rules
% 4.41/1.79  ----------------------
% 4.41/1.79  #Ref     : 0
% 4.41/1.79  #Sup     : 353
% 4.41/1.79  #Fact    : 0
% 4.41/1.79  #Define  : 0
% 4.41/1.79  #Split   : 65
% 4.41/1.79  #Chain   : 0
% 4.41/1.79  #Close   : 0
% 4.41/1.79  
% 4.41/1.79  Ordering : KBO
% 4.41/1.79  
% 4.41/1.79  Simplification rules
% 4.41/1.79  ----------------------
% 4.41/1.79  #Subsume      : 140
% 4.41/1.79  #Demod        : 504
% 4.41/1.79  #Tautology    : 119
% 4.41/1.79  #SimpNegUnit  : 13
% 4.41/1.79  #BackRed      : 21
% 4.41/1.79  
% 4.41/1.79  #Partial instantiations: 0
% 4.41/1.79  #Strategies tried      : 1
% 4.41/1.79  
% 4.41/1.79  Timing (in seconds)
% 4.41/1.79  ----------------------
% 4.41/1.80  Preprocessing        : 0.34
% 4.41/1.80  Parsing              : 0.19
% 4.41/1.80  CNF conversion       : 0.02
% 4.41/1.80  Main loop            : 0.62
% 4.41/1.80  Inferencing          : 0.22
% 4.41/1.80  Reduction            : 0.20
% 4.41/1.80  Demodulation         : 0.13
% 4.41/1.80  BG Simplification    : 0.03
% 4.41/1.80  Subsumption          : 0.13
% 4.41/1.80  Abstraction          : 0.03
% 4.41/1.80  MUC search           : 0.00
% 4.41/1.80  Cooper               : 0.00
% 4.41/1.80  Total                : 1.02
% 4.41/1.80  Index Insertion      : 0.00
% 4.41/1.80  Index Deletion       : 0.00
% 4.41/1.80  Index Matching       : 0.00
% 4.41/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
