%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:26 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 376 expanded)
%              Number of leaves         :   27 ( 143 expanded)
%              Depth                    :    8
%              Number of atoms          :  329 (1597 expanded)
%              Number of equality atoms :   48 (  94 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_105,axiom,(
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

tff(c_44,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1663,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
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

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_111,plain,(
    ! [A_60,B_61] :
      ( k1_tops_1(A_60,k2_pre_topc(A_60,B_61)) = B_61
      | ~ v6_tops_1(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_115,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_111])).

tff(c_121,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_115])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_56,B_57] :
      ( k1_tops_1(A_56,k1_tops_1(A_56,B_57)) = k1_tops_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_166,plain,(
    ! [A_68,B_69] :
      ( k1_tops_1(A_68,k1_tops_1(A_68,k2_pre_topc(A_68,B_69))) = k1_tops_1(A_68,k2_pre_topc(A_68,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_170,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_166])).

tff(c_176,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121,c_121,c_170])).

tff(c_24,plain,(
    ! [C_28,A_16,D_30,B_24] :
      ( v3_pre_topc(C_28,A_16)
      | k1_tops_1(A_16,C_28) != C_28
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0(B_24)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_288,plain,(
    ! [D_83,B_84] :
      ( ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(B_84)))
      | ~ l1_pre_topc(B_84) ) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_291,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_288])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_291])).

tff(c_300,plain,(
    ! [C_85,A_86] :
      ( v3_pre_topc(C_85,A_86)
      | k1_tops_1(A_86,C_85) != C_85
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86) ) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_306,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_300])).

tff(c_313,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_176,c_306])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_313])).

tff(c_316,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_320,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_323,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(B_87,k2_pre_topc(A_88,B_87))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_325,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_323])).

tff(c_330,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_325])).

tff(c_368,plain,(
    ! [A_93,B_94] :
      ( k1_tops_1(A_93,k2_pre_topc(A_93,B_94)) = B_94
      | ~ v6_tops_1(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_372,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_368])).

tff(c_378,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_372])).

tff(c_346,plain,(
    ! [A_91,B_92] :
      ( k1_tops_1(A_91,k1_tops_1(A_91,B_92)) = k1_tops_1(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_425,plain,(
    ! [A_103,B_104] :
      ( k1_tops_1(A_103,k1_tops_1(A_103,k2_pre_topc(A_103,B_104))) = k1_tops_1(A_103,k2_pre_topc(A_103,B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_8,c_346])).

tff(c_429,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_425])).

tff(c_435,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_378,c_378,c_429])).

tff(c_641,plain,(
    ! [B_130,A_131] :
      ( v4_tops_1(B_130,A_131)
      | ~ r1_tarski(B_130,k2_pre_topc(A_131,k1_tops_1(A_131,B_130)))
      | ~ r1_tarski(k1_tops_1(A_131,k2_pre_topc(A_131,B_130)),B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_647,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_641])).

tff(c_650,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_330,c_435,c_647])).

tff(c_652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_650])).

tff(c_653,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_317,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_654,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_656,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_654,c_42])).

tff(c_657,plain,(
    ! [B_132,A_133] :
      ( r1_tarski(B_132,k2_pre_topc(A_133,B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_661,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_657])).

tff(c_667,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_661])).

tff(c_850,plain,(
    ! [B_156,A_157,C_158] :
      ( r1_tarski(B_156,k1_tops_1(A_157,C_158))
      | ~ r1_tarski(B_156,C_158)
      | ~ v3_pre_topc(B_156,A_157)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_980,plain,(
    ! [B_177,A_178,B_179] :
      ( r1_tarski(B_177,k1_tops_1(A_178,k2_pre_topc(A_178,B_179)))
      | ~ r1_tarski(B_177,k2_pre_topc(A_178,B_179))
      | ~ v3_pre_topc(B_177,A_178)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_8,c_850])).

tff(c_730,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k1_tops_1(A_144,k2_pre_topc(A_144,B_145)),B_145)
      | ~ v4_tops_1(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_736,plain,(
    ! [A_144,B_145] :
      ( k1_tops_1(A_144,k2_pre_topc(A_144,B_145)) = B_145
      | ~ r1_tarski(B_145,k1_tops_1(A_144,k2_pre_topc(A_144,B_145)))
      | ~ v4_tops_1(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_730,c_2])).

tff(c_1027,plain,(
    ! [A_182,B_183] :
      ( k1_tops_1(A_182,k2_pre_topc(A_182,B_183)) = B_183
      | ~ v4_tops_1(B_183,A_182)
      | ~ r1_tarski(B_183,k2_pre_topc(A_182,B_183))
      | ~ v3_pre_topc(B_183,A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(resolution,[status(thm)],[c_980,c_736])).

tff(c_1031,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_667,c_1027])).

tff(c_1037,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_653,c_656,c_1031])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( v6_tops_1(B_13,A_11)
      | k1_tops_1(A_11,k2_pre_topc(A_11,B_13)) != B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1063,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1037,c_18])).

tff(c_1080,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1063])).

tff(c_1082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1080])).

tff(c_1083,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1084,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1085,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1084,c_48])).

tff(c_1095,plain,(
    ! [B_186,A_187] :
      ( r1_tarski(B_186,k2_pre_topc(A_187,B_186))
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1099,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1095])).

tff(c_1105,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1099])).

tff(c_1386,plain,(
    ! [B_219,A_220,C_221] :
      ( r1_tarski(B_219,k1_tops_1(A_220,C_221))
      | ~ r1_tarski(B_219,C_221)
      | ~ v3_pre_topc(B_219,A_220)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1561,plain,(
    ! [B_240,A_241,B_242] :
      ( r1_tarski(B_240,k1_tops_1(A_241,k2_pre_topc(A_241,B_242)))
      | ~ r1_tarski(B_240,k2_pre_topc(A_241,B_242))
      | ~ v3_pre_topc(B_240,A_241)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_8,c_1386])).

tff(c_1159,plain,(
    ! [A_198,B_199] :
      ( r1_tarski(k1_tops_1(A_198,k2_pre_topc(A_198,B_199)),B_199)
      | ~ v4_tops_1(B_199,A_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1162,plain,(
    ! [A_198,B_199] :
      ( k1_tops_1(A_198,k2_pre_topc(A_198,B_199)) = B_199
      | ~ r1_tarski(B_199,k1_tops_1(A_198,k2_pre_topc(A_198,B_199)))
      | ~ v4_tops_1(B_199,A_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(resolution,[status(thm)],[c_1159,c_2])).

tff(c_1596,plain,(
    ! [A_247,B_248] :
      ( k1_tops_1(A_247,k2_pre_topc(A_247,B_248)) = B_248
      | ~ v4_tops_1(B_248,A_247)
      | ~ r1_tarski(B_248,k2_pre_topc(A_247,B_248))
      | ~ v3_pre_topc(B_248,A_247)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(resolution,[status(thm)],[c_1561,c_1162])).

tff(c_1600,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1105,c_1596])).

tff(c_1606,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1083,c_1085,c_1600])).

tff(c_1632,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1606,c_18])).

tff(c_1649,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1632])).

tff(c_1651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1649])).

tff(c_1652,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1712,plain,(
    ! [A_259,B_260] :
      ( k1_tops_1(A_259,k2_pre_topc(A_259,B_260)) = B_260
      | ~ v6_tops_1(B_260,A_259)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1716,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1712])).

tff(c_1722,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1652,c_1716])).

tff(c_1689,plain,(
    ! [A_255,B_256] :
      ( k1_tops_1(A_255,k1_tops_1(A_255,B_256)) = k1_tops_1(A_255,B_256)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1786,plain,(
    ! [A_267,B_268] :
      ( k1_tops_1(A_267,k1_tops_1(A_267,k2_pre_topc(A_267,B_268))) = k1_tops_1(A_267,k2_pre_topc(A_267,B_268))
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(resolution,[status(thm)],[c_8,c_1689])).

tff(c_1790,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1786])).

tff(c_1796,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1722,c_1722,c_1790])).

tff(c_1876,plain,(
    ! [D_277,B_278] :
      ( ~ m1_subset_1(D_277,k1_zfmisc_1(u1_struct_0(B_278)))
      | ~ l1_pre_topc(B_278) ) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_1879,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1876])).

tff(c_1886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1879])).

tff(c_1888,plain,(
    ! [C_279,A_280] :
      ( v3_pre_topc(C_279,A_280)
      | k1_tops_1(A_280,C_279) != C_279
      | ~ m1_subset_1(C_279,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280) ) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1894,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1888])).

tff(c_1901,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1796,c_1894])).

tff(c_1903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1663,c_1901])).

tff(c_1905,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1904,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1906,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1904])).

tff(c_1911,plain,(
    ! [B_281,A_282] :
      ( r1_tarski(B_281,k2_pre_topc(A_282,B_281))
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1913,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1911])).

tff(c_1918,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1913])).

tff(c_1957,plain,(
    ! [A_289,B_290] :
      ( k1_tops_1(A_289,k2_pre_topc(A_289,B_290)) = B_290
      | ~ v6_tops_1(B_290,A_289)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_289)))
      | ~ l1_pre_topc(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1961,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1957])).

tff(c_1967,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1652,c_1961])).

tff(c_1934,plain,(
    ! [A_285,B_286] :
      ( k1_tops_1(A_285,k1_tops_1(A_285,B_286)) = k1_tops_1(A_285,B_286)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2031,plain,(
    ! [A_297,B_298] :
      ( k1_tops_1(A_297,k1_tops_1(A_297,k2_pre_topc(A_297,B_298))) = k1_tops_1(A_297,k2_pre_topc(A_297,B_298))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297) ) ),
    inference(resolution,[status(thm)],[c_8,c_1934])).

tff(c_2035,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2031])).

tff(c_2041,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1967,c_1967,c_2035])).

tff(c_2162,plain,(
    ! [B_312,A_313] :
      ( v4_tops_1(B_312,A_313)
      | ~ r1_tarski(B_312,k2_pre_topc(A_313,k1_tops_1(A_313,B_312)))
      | ~ r1_tarski(k1_tops_1(A_313,k2_pre_topc(A_313,B_312)),B_312)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2171,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1967,c_2162])).

tff(c_2176,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_1918,c_2041,c_2171])).

tff(c_2178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1906,c_2176])).

tff(c_2180,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1904])).

tff(c_1653,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_2180,c_1653,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 14:09:55 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.73  
% 4.28/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.74  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.28/1.74  
% 4.28/1.74  %Foreground sorts:
% 4.28/1.74  
% 4.28/1.74  
% 4.28/1.74  %Background operators:
% 4.28/1.74  
% 4.28/1.74  
% 4.28/1.74  %Foreground operators:
% 4.28/1.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.28/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.74  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 4.28/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.28/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.74  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 4.28/1.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.28/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.28/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.28/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.28/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.28/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.28/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.28/1.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.28/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.28/1.74  
% 4.28/1.76  tff(f_131, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 4.28/1.76  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 4.28/1.76  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.28/1.76  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 4.28/1.76  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 4.28/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.28/1.76  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.28/1.76  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 4.28/1.76  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 4.28/1.76  tff(c_44, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_1663, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.28/1.76  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_46, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_53, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 4.28/1.76  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_64, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.28/1.76  tff(c_50, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_54, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 4.28/1.76  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_111, plain, (![A_60, B_61]: (k1_tops_1(A_60, k2_pre_topc(A_60, B_61))=B_61 | ~v6_tops_1(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.76  tff(c_115, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_111])).
% 4.28/1.76  tff(c_121, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_115])).
% 4.28/1.76  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.76  tff(c_88, plain, (![A_56, B_57]: (k1_tops_1(A_56, k1_tops_1(A_56, B_57))=k1_tops_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.28/1.76  tff(c_166, plain, (![A_68, B_69]: (k1_tops_1(A_68, k1_tops_1(A_68, k2_pre_topc(A_68, B_69)))=k1_tops_1(A_68, k2_pre_topc(A_68, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_8, c_88])).
% 4.28/1.76  tff(c_170, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_166])).
% 4.28/1.76  tff(c_176, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121, c_121, c_170])).
% 4.28/1.76  tff(c_24, plain, (![C_28, A_16, D_30, B_24]: (v3_pre_topc(C_28, A_16) | k1_tops_1(A_16, C_28)!=C_28 | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0(B_24))) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(B_24) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.28/1.76  tff(c_288, plain, (![D_83, B_84]: (~m1_subset_1(D_83, k1_zfmisc_1(u1_struct_0(B_84))) | ~l1_pre_topc(B_84))), inference(splitLeft, [status(thm)], [c_24])).
% 4.28/1.76  tff(c_291, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_288])).
% 4.28/1.76  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_291])).
% 4.28/1.76  tff(c_300, plain, (![C_85, A_86]: (v3_pre_topc(C_85, A_86) | k1_tops_1(A_86, C_85)!=C_85 | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86))), inference(splitRight, [status(thm)], [c_24])).
% 4.28/1.76  tff(c_306, plain, (v3_pre_topc('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_300])).
% 4.28/1.76  tff(c_313, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_176, c_306])).
% 4.28/1.76  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_313])).
% 4.28/1.76  tff(c_316, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.28/1.76  tff(c_320, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_316])).
% 4.28/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.76  tff(c_323, plain, (![B_87, A_88]: (r1_tarski(B_87, k2_pre_topc(A_88, B_87)) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.76  tff(c_325, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_323])).
% 4.28/1.76  tff(c_330, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_325])).
% 4.28/1.76  tff(c_368, plain, (![A_93, B_94]: (k1_tops_1(A_93, k2_pre_topc(A_93, B_94))=B_94 | ~v6_tops_1(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.76  tff(c_372, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_368])).
% 4.28/1.76  tff(c_378, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_372])).
% 4.28/1.76  tff(c_346, plain, (![A_91, B_92]: (k1_tops_1(A_91, k1_tops_1(A_91, B_92))=k1_tops_1(A_91, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.28/1.76  tff(c_425, plain, (![A_103, B_104]: (k1_tops_1(A_103, k1_tops_1(A_103, k2_pre_topc(A_103, B_104)))=k1_tops_1(A_103, k2_pre_topc(A_103, B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_8, c_346])).
% 4.28/1.76  tff(c_429, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_425])).
% 4.28/1.76  tff(c_435, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_378, c_378, c_429])).
% 4.28/1.76  tff(c_641, plain, (![B_130, A_131]: (v4_tops_1(B_130, A_131) | ~r1_tarski(B_130, k2_pre_topc(A_131, k1_tops_1(A_131, B_130))) | ~r1_tarski(k1_tops_1(A_131, k2_pre_topc(A_131, B_130)), B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.28/1.76  tff(c_647, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_378, c_641])).
% 4.28/1.76  tff(c_650, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_6, c_330, c_435, c_647])).
% 4.28/1.76  tff(c_652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_650])).
% 4.28/1.76  tff(c_653, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_316])).
% 4.28/1.76  tff(c_317, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.28/1.76  tff(c_654, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_316])).
% 4.28/1.76  tff(c_42, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_656, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_654, c_42])).
% 4.28/1.76  tff(c_657, plain, (![B_132, A_133]: (r1_tarski(B_132, k2_pre_topc(A_133, B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.76  tff(c_661, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_657])).
% 4.28/1.76  tff(c_667, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_661])).
% 4.28/1.76  tff(c_850, plain, (![B_156, A_157, C_158]: (r1_tarski(B_156, k1_tops_1(A_157, C_158)) | ~r1_tarski(B_156, C_158) | ~v3_pre_topc(B_156, A_157) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.28/1.76  tff(c_980, plain, (![B_177, A_178, B_179]: (r1_tarski(B_177, k1_tops_1(A_178, k2_pre_topc(A_178, B_179))) | ~r1_tarski(B_177, k2_pre_topc(A_178, B_179)) | ~v3_pre_topc(B_177, A_178) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_178))) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(resolution, [status(thm)], [c_8, c_850])).
% 4.28/1.76  tff(c_730, plain, (![A_144, B_145]: (r1_tarski(k1_tops_1(A_144, k2_pre_topc(A_144, B_145)), B_145) | ~v4_tops_1(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.28/1.76  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.76  tff(c_736, plain, (![A_144, B_145]: (k1_tops_1(A_144, k2_pre_topc(A_144, B_145))=B_145 | ~r1_tarski(B_145, k1_tops_1(A_144, k2_pre_topc(A_144, B_145))) | ~v4_tops_1(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_730, c_2])).
% 4.28/1.76  tff(c_1027, plain, (![A_182, B_183]: (k1_tops_1(A_182, k2_pre_topc(A_182, B_183))=B_183 | ~v4_tops_1(B_183, A_182) | ~r1_tarski(B_183, k2_pre_topc(A_182, B_183)) | ~v3_pre_topc(B_183, A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(resolution, [status(thm)], [c_980, c_736])).
% 4.28/1.76  tff(c_1031, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_667, c_1027])).
% 4.28/1.76  tff(c_1037, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_653, c_656, c_1031])).
% 4.28/1.76  tff(c_18, plain, (![B_13, A_11]: (v6_tops_1(B_13, A_11) | k1_tops_1(A_11, k2_pre_topc(A_11, B_13))!=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.76  tff(c_1063, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1037, c_18])).
% 4.28/1.76  tff(c_1080, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1063])).
% 4.28/1.76  tff(c_1082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1080])).
% 4.28/1.76  tff(c_1083, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 4.28/1.76  tff(c_1084, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.28/1.76  tff(c_48, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_1085, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1084, c_48])).
% 4.28/1.76  tff(c_1095, plain, (![B_186, A_187]: (r1_tarski(B_186, k2_pre_topc(A_187, B_186)) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.76  tff(c_1099, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1095])).
% 4.28/1.76  tff(c_1105, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1099])).
% 4.28/1.76  tff(c_1386, plain, (![B_219, A_220, C_221]: (r1_tarski(B_219, k1_tops_1(A_220, C_221)) | ~r1_tarski(B_219, C_221) | ~v3_pre_topc(B_219, A_220) | ~m1_subset_1(C_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.28/1.76  tff(c_1561, plain, (![B_240, A_241, B_242]: (r1_tarski(B_240, k1_tops_1(A_241, k2_pre_topc(A_241, B_242))) | ~r1_tarski(B_240, k2_pre_topc(A_241, B_242)) | ~v3_pre_topc(B_240, A_241) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_241))) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_8, c_1386])).
% 4.28/1.76  tff(c_1159, plain, (![A_198, B_199]: (r1_tarski(k1_tops_1(A_198, k2_pre_topc(A_198, B_199)), B_199) | ~v4_tops_1(B_199, A_198) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.28/1.76  tff(c_1162, plain, (![A_198, B_199]: (k1_tops_1(A_198, k2_pre_topc(A_198, B_199))=B_199 | ~r1_tarski(B_199, k1_tops_1(A_198, k2_pre_topc(A_198, B_199))) | ~v4_tops_1(B_199, A_198) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(resolution, [status(thm)], [c_1159, c_2])).
% 4.28/1.76  tff(c_1596, plain, (![A_247, B_248]: (k1_tops_1(A_247, k2_pre_topc(A_247, B_248))=B_248 | ~v4_tops_1(B_248, A_247) | ~r1_tarski(B_248, k2_pre_topc(A_247, B_248)) | ~v3_pre_topc(B_248, A_247) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(resolution, [status(thm)], [c_1561, c_1162])).
% 4.28/1.76  tff(c_1600, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1105, c_1596])).
% 4.28/1.76  tff(c_1606, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1083, c_1085, c_1600])).
% 4.28/1.76  tff(c_1632, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1606, c_18])).
% 4.28/1.76  tff(c_1649, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1632])).
% 4.28/1.76  tff(c_1651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1649])).
% 4.28/1.76  tff(c_1652, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.28/1.76  tff(c_1712, plain, (![A_259, B_260]: (k1_tops_1(A_259, k2_pre_topc(A_259, B_260))=B_260 | ~v6_tops_1(B_260, A_259) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.76  tff(c_1716, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1712])).
% 4.28/1.76  tff(c_1722, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1652, c_1716])).
% 4.28/1.76  tff(c_1689, plain, (![A_255, B_256]: (k1_tops_1(A_255, k1_tops_1(A_255, B_256))=k1_tops_1(A_255, B_256) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.28/1.76  tff(c_1786, plain, (![A_267, B_268]: (k1_tops_1(A_267, k1_tops_1(A_267, k2_pre_topc(A_267, B_268)))=k1_tops_1(A_267, k2_pre_topc(A_267, B_268)) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267))), inference(resolution, [status(thm)], [c_8, c_1689])).
% 4.28/1.76  tff(c_1790, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1786])).
% 4.28/1.76  tff(c_1796, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1722, c_1722, c_1790])).
% 4.28/1.76  tff(c_1876, plain, (![D_277, B_278]: (~m1_subset_1(D_277, k1_zfmisc_1(u1_struct_0(B_278))) | ~l1_pre_topc(B_278))), inference(splitLeft, [status(thm)], [c_24])).
% 4.28/1.76  tff(c_1879, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1876])).
% 4.28/1.76  tff(c_1886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1879])).
% 4.28/1.76  tff(c_1888, plain, (![C_279, A_280]: (v3_pre_topc(C_279, A_280) | k1_tops_1(A_280, C_279)!=C_279 | ~m1_subset_1(C_279, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280))), inference(splitRight, [status(thm)], [c_24])).
% 4.28/1.76  tff(c_1894, plain, (v3_pre_topc('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1888])).
% 4.28/1.76  tff(c_1901, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1796, c_1894])).
% 4.28/1.76  tff(c_1903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1663, c_1901])).
% 4.28/1.76  tff(c_1905, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.28/1.76  tff(c_1904, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.28/1.76  tff(c_1906, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1904])).
% 4.28/1.76  tff(c_1911, plain, (![B_281, A_282]: (r1_tarski(B_281, k2_pre_topc(A_282, B_281)) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.76  tff(c_1913, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1911])).
% 4.28/1.76  tff(c_1918, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1913])).
% 4.28/1.76  tff(c_1957, plain, (![A_289, B_290]: (k1_tops_1(A_289, k2_pre_topc(A_289, B_290))=B_290 | ~v6_tops_1(B_290, A_289) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_289))) | ~l1_pre_topc(A_289))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.76  tff(c_1961, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1957])).
% 4.28/1.76  tff(c_1967, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1652, c_1961])).
% 4.28/1.76  tff(c_1934, plain, (![A_285, B_286]: (k1_tops_1(A_285, k1_tops_1(A_285, B_286))=k1_tops_1(A_285, B_286) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(A_285))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.28/1.76  tff(c_2031, plain, (![A_297, B_298]: (k1_tops_1(A_297, k1_tops_1(A_297, k2_pre_topc(A_297, B_298)))=k1_tops_1(A_297, k2_pre_topc(A_297, B_298)) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297))), inference(resolution, [status(thm)], [c_8, c_1934])).
% 4.28/1.76  tff(c_2035, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2031])).
% 4.28/1.76  tff(c_2041, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1967, c_1967, c_2035])).
% 4.28/1.76  tff(c_2162, plain, (![B_312, A_313]: (v4_tops_1(B_312, A_313) | ~r1_tarski(B_312, k2_pre_topc(A_313, k1_tops_1(A_313, B_312))) | ~r1_tarski(k1_tops_1(A_313, k2_pre_topc(A_313, B_312)), B_312) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_313))) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.28/1.76  tff(c_2171, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1967, c_2162])).
% 4.28/1.76  tff(c_2176, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_6, c_1918, c_2041, c_2171])).
% 4.28/1.76  tff(c_2178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1906, c_2176])).
% 4.28/1.76  tff(c_2180, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1904])).
% 4.28/1.76  tff(c_1653, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.28/1.76  tff(c_40, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.28/1.76  tff(c_2182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1905, c_2180, c_1653, c_40])).
% 4.28/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.76  
% 4.28/1.76  Inference rules
% 4.28/1.76  ----------------------
% 4.28/1.76  #Ref     : 0
% 4.28/1.76  #Sup     : 436
% 4.28/1.76  #Fact    : 0
% 4.28/1.76  #Define  : 0
% 4.28/1.76  #Split   : 66
% 4.28/1.76  #Chain   : 0
% 4.28/1.76  #Close   : 0
% 4.28/1.76  
% 4.28/1.76  Ordering : KBO
% 4.28/1.76  
% 4.28/1.76  Simplification rules
% 4.28/1.76  ----------------------
% 4.28/1.76  #Subsume      : 124
% 4.28/1.76  #Demod        : 574
% 4.28/1.76  #Tautology    : 177
% 4.28/1.76  #SimpNegUnit  : 12
% 4.28/1.76  #BackRed      : 10
% 4.28/1.76  
% 4.28/1.76  #Partial instantiations: 0
% 4.28/1.76  #Strategies tried      : 1
% 4.28/1.76  
% 4.28/1.76  Timing (in seconds)
% 4.28/1.76  ----------------------
% 4.28/1.77  Preprocessing        : 0.32
% 4.28/1.77  Parsing              : 0.17
% 4.28/1.77  CNF conversion       : 0.02
% 4.28/1.77  Main loop            : 0.65
% 4.28/1.77  Inferencing          : 0.22
% 4.28/1.77  Reduction            : 0.21
% 4.28/1.77  Demodulation         : 0.15
% 4.28/1.77  BG Simplification    : 0.03
% 4.28/1.77  Subsumption          : 0.13
% 4.28/1.77  Abstraction          : 0.03
% 4.28/1.77  MUC search           : 0.00
% 4.28/1.77  Cooper               : 0.00
% 4.28/1.77  Total                : 1.03
% 4.28/1.77  Index Insertion      : 0.00
% 4.28/1.77  Index Deletion       : 0.00
% 4.28/1.77  Index Matching       : 0.00
% 4.28/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
