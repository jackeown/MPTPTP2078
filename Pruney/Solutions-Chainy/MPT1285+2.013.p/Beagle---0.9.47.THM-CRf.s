%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:25 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 594 expanded)
%              Number of leaves         :   27 ( 216 expanded)
%              Depth                    :   15
%              Number of atoms          :  455 (2603 expanded)
%              Number of equality atoms :   64 ( 153 expanded)
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

tff(f_129,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_103,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_44,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4017,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_53,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3392,plain,(
    ! [B_277,A_278] :
      ( r1_tarski(B_277,k2_pre_topc(A_278,B_277))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3396,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_3392])).

tff(c_3402,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3396])).

tff(c_782,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(B_120,k2_pre_topc(A_121,B_120))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_786,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_782])).

tff(c_792,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_786])).

tff(c_64,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_54,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

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

tff(c_26,plain,(
    ! [C_35,A_23,D_37,B_31] :
      ( v3_pre_topc(C_35,A_23)
      | k1_tops_1(A_23,C_35) != C_35
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0(B_31)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(B_31)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_303,plain,(
    ! [D_77,B_78] :
      ( ~ m1_subset_1(D_77,k1_zfmisc_1(u1_struct_0(B_78)))
      | ~ l1_pre_topc(B_78) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_306,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_303])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_306])).

tff(c_315,plain,(
    ! [C_79,A_80] :
      ( v3_pre_topc(C_79,A_80)
      | k1_tops_1(A_80,C_79) != C_79
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_321,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_315])).

tff(c_328,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_176,c_321])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_328])).

tff(c_332,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_331,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_335,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_338,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,k2_pre_topc(A_82,B_81))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_340,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_338])).

tff(c_345,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_340])).

tff(c_383,plain,(
    ! [A_87,B_88] :
      ( k1_tops_1(A_87,k2_pre_topc(A_87,B_88)) = B_88
      | ~ v6_tops_1(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_387,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_383])).

tff(c_393,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_387])).

tff(c_361,plain,(
    ! [A_85,B_86] :
      ( k1_tops_1(A_85,k1_tops_1(A_85,B_86)) = k1_tops_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_440,plain,(
    ! [A_97,B_98] :
      ( k1_tops_1(A_97,k1_tops_1(A_97,k2_pre_topc(A_97,B_98))) = k1_tops_1(A_97,k2_pre_topc(A_97,B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_8,c_361])).

tff(c_444,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_440])).

tff(c_450,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_393,c_393,c_444])).

tff(c_753,plain,(
    ! [B_118,A_119] :
      ( v4_tops_1(B_118,A_119)
      | ~ r1_tarski(B_118,k2_pre_topc(A_119,k1_tops_1(A_119,B_118)))
      | ~ r1_tarski(k1_tops_1(A_119,k2_pre_topc(A_119,B_118)),B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_767,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_753])).

tff(c_775,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_345,c_450,c_767])).

tff(c_777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_775])).

tff(c_779,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_781,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_779,c_42])).

tff(c_778,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_28,plain,(
    ! [B_31,D_37,C_35,A_23] :
      ( k1_tops_1(B_31,D_37) = D_37
      | ~ v3_pre_topc(D_37,B_31)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0(B_31)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(B_31)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2990,plain,(
    ! [C_253,A_254] :
      ( ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254)
      | ~ v2_pre_topc(A_254) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_3002,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2990])).

tff(c_3016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3002])).

tff(c_3018,plain,(
    ! [B_255,D_256] :
      ( k1_tops_1(B_255,D_256) = D_256
      | ~ v3_pre_topc(D_256,B_255)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(u1_struct_0(B_255)))
      | ~ l1_pre_topc(B_255) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3033,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_3018])).

tff(c_3046,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_778,c_3033])).

tff(c_828,plain,(
    ! [A_128,B_129] :
      ( k1_tops_1(A_128,k2_pre_topc(A_128,B_129)) = B_129
      | ~ v6_tops_1(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_832,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_828])).

tff(c_838,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_832])).

tff(c_919,plain,(
    ! [A_138,B_139,C_140] :
      ( r1_tarski(k1_tops_1(A_138,B_139),k1_tops_1(A_138,C_140))
      | ~ r1_tarski(B_139,C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_939,plain,(
    ! [B_139] :
      ( r1_tarski(k1_tops_1('#skF_1',B_139),'#skF_3')
      | ~ r1_tarski(B_139,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_919])).

tff(c_958,plain,(
    ! [B_139] :
      ( r1_tarski(k1_tops_1('#skF_1',B_139),'#skF_3')
      | ~ r1_tarski(B_139,k2_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_939])).

tff(c_1030,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_1033,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1030])).

tff(c_1037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1033])).

tff(c_1039,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_1082,plain,(
    ! [C_148,A_149] :
      ( ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_1085,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1039,c_1082])).

tff(c_1098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1085])).

tff(c_1100,plain,(
    ! [B_150,D_151] :
      ( k1_tops_1(B_150,D_151) = D_151
      | ~ v3_pre_topc(D_151,B_150)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0(B_150)))
      | ~ l1_pre_topc(B_150) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1112,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1100])).

tff(c_1123,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_778,c_1112])).

tff(c_805,plain,(
    ! [A_124,B_125] :
      ( k1_tops_1(A_124,k1_tops_1(A_124,B_125)) = k1_tops_1(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_811,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_805])).

tff(c_818,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_811])).

tff(c_864,plain,(
    ! [B_134,A_135] :
      ( r1_tarski(B_134,k2_pre_topc(A_135,k1_tops_1(A_135,B_134)))
      | ~ v4_tops_1(B_134,A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_872,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')))
    | ~ v4_tops_1(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_864])).

tff(c_880,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')))
    | ~ v4_tops_1(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_872])).

tff(c_918,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_880])).

tff(c_1124,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_918])).

tff(c_1128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1124])).

tff(c_1130,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_880])).

tff(c_2805,plain,(
    ! [A_242,B_243,C_244] :
      ( r1_tarski(k1_tops_1(A_242,B_243),k1_tops_1(A_242,C_244))
      | ~ r1_tarski(B_243,C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2828,plain,(
    ! [C_244] :
      ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2',C_244))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_2805])).

tff(c_2846,plain,(
    ! [C_244] :
      ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2',C_244))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1130,c_2828])).

tff(c_3098,plain,(
    ! [C_258] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_258))
      | ~ r1_tarski('#skF_4',C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3046,c_3046,c_2846])).

tff(c_3105,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_3098])).

tff(c_3113,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3105])).

tff(c_855,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(k1_tops_1(A_132,k2_pre_topc(A_132,B_133)),B_133)
      | ~ v4_tops_1(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3285,plain,(
    ! [A_273,B_274] :
      ( k1_tops_1(A_273,k2_pre_topc(A_273,B_274)) = B_274
      | ~ r1_tarski(B_274,k1_tops_1(A_273,k2_pre_topc(A_273,B_274)))
      | ~ v4_tops_1(B_274,A_273)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273) ) ),
    inference(resolution,[status(thm)],[c_855,c_2])).

tff(c_3297,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_3113,c_3285])).

tff(c_3313,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_792,c_34,c_781,c_3297])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( v6_tops_1(B_13,A_11)
      | k1_tops_1(A_11,k2_pre_topc(A_11,B_13)) != B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3356,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3313,c_18])).

tff(c_3377,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_3356])).

tff(c_3379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_3377])).

tff(c_3381,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3382,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3381,c_48])).

tff(c_3380,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3719,plain,(
    ! [C_311,A_312] :
      ( ~ m1_subset_1(C_311,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_3728,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3719])).

tff(c_3739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3728])).

tff(c_3741,plain,(
    ! [B_313,D_314] :
      ( k1_tops_1(B_313,D_314) = D_314
      | ~ v3_pre_topc(D_314,B_313)
      | ~ m1_subset_1(D_314,k1_zfmisc_1(u1_struct_0(B_313)))
      | ~ l1_pre_topc(B_313) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3753,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_3741])).

tff(c_3763,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3380,c_3753])).

tff(c_24,plain,(
    ! [A_16,B_20,C_22] :
      ( r1_tarski(k1_tops_1(A_16,B_20),k1_tops_1(A_16,C_22))
      | ~ r1_tarski(B_20,C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3776,plain,(
    ! [C_22] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_22))
      | ~ r1_tarski('#skF_4',C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3763,c_24])).

tff(c_3793,plain,(
    ! [C_315] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_315))
      | ~ r1_tarski('#skF_4',C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_3776])).

tff(c_3797,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_3793])).

tff(c_3803,plain,(
    ! [B_4] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2',B_4)))
      | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3797])).

tff(c_3456,plain,(
    ! [A_289,B_290] :
      ( r1_tarski(k1_tops_1(A_289,k2_pre_topc(A_289,B_290)),B_290)
      | ~ v4_tops_1(B_290,A_289)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_289)))
      | ~ l1_pre_topc(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3935,plain,(
    ! [A_333,B_334] :
      ( k1_tops_1(A_333,k2_pre_topc(A_333,B_334)) = B_334
      | ~ r1_tarski(B_334,k1_tops_1(A_333,k2_pre_topc(A_333,B_334)))
      | ~ v4_tops_1(B_334,A_333)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ l1_pre_topc(A_333) ) ),
    inference(resolution,[status(thm)],[c_3456,c_2])).

tff(c_3939,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_3803,c_3935])).

tff(c_3946,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3402,c_34,c_3382,c_3939])).

tff(c_3979,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3946,c_18])).

tff(c_4002,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_3979])).

tff(c_4004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_4002])).

tff(c_4005,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4066,plain,(
    ! [A_345,B_346] :
      ( k1_tops_1(A_345,k2_pre_topc(A_345,B_346)) = B_346
      | ~ v6_tops_1(B_346,A_345)
      | ~ m1_subset_1(B_346,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ l1_pre_topc(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4070,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4066])).

tff(c_4076,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4005,c_4070])).

tff(c_4043,plain,(
    ! [A_341,B_342] :
      ( k1_tops_1(A_341,k1_tops_1(A_341,B_342)) = k1_tops_1(A_341,B_342)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4140,plain,(
    ! [A_353,B_354] :
      ( k1_tops_1(A_353,k1_tops_1(A_353,k2_pre_topc(A_353,B_354))) = k1_tops_1(A_353,k2_pre_topc(A_353,B_354))
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ l1_pre_topc(A_353) ) ),
    inference(resolution,[status(thm)],[c_8,c_4043])).

tff(c_4144,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4140])).

tff(c_4150,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4076,c_4076,c_4144])).

tff(c_4006,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4072,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v6_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_4066])).

tff(c_4079,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4006,c_4072])).

tff(c_4178,plain,(
    ! [A_355,B_356,C_357] :
      ( r1_tarski(k1_tops_1(A_355,B_356),k1_tops_1(A_355,C_357))
      | ~ r1_tarski(B_356,C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ l1_pre_topc(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4195,plain,(
    ! [C_357] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_357))
      | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4079,c_4178])).

tff(c_4215,plain,(
    ! [C_357] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_357))
      | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),C_357)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4195])).

tff(c_4295,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4215])).

tff(c_4298,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_4295])).

tff(c_4302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_4298])).

tff(c_4304,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_4215])).

tff(c_4364,plain,(
    ! [D_366,B_367] :
      ( ~ m1_subset_1(D_366,k1_zfmisc_1(u1_struct_0(B_367)))
      | ~ l1_pre_topc(B_367) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_4367,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4304,c_4364])).

tff(c_4377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4367])).

tff(c_4421,plain,(
    ! [C_370,A_371] :
      ( v3_pre_topc(C_370,A_371)
      | k1_tops_1(A_371,C_370) != C_370
      | ~ m1_subset_1(C_370,k1_zfmisc_1(u1_struct_0(A_371)))
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_4430,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4421])).

tff(c_4441,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_4150,c_4430])).

tff(c_4443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4017,c_4441])).

tff(c_4445,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4444,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4446,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4444])).

tff(c_4451,plain,(
    ! [B_372,A_373] :
      ( r1_tarski(B_372,k2_pre_topc(A_373,B_372))
      | ~ m1_subset_1(B_372,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ l1_pre_topc(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4453,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4451])).

tff(c_4458,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4453])).

tff(c_4497,plain,(
    ! [A_380,B_381] :
      ( k1_tops_1(A_380,k2_pre_topc(A_380,B_381)) = B_381
      | ~ v6_tops_1(B_381,A_380)
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ l1_pre_topc(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4501,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4497])).

tff(c_4507,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4005,c_4501])).

tff(c_4474,plain,(
    ! [A_376,B_377] :
      ( k1_tops_1(A_376,k1_tops_1(A_376,B_377)) = k1_tops_1(A_376,B_377)
      | ~ m1_subset_1(B_377,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ l1_pre_topc(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4571,plain,(
    ! [A_388,B_389] :
      ( k1_tops_1(A_388,k1_tops_1(A_388,k2_pre_topc(A_388,B_389))) = k1_tops_1(A_388,k2_pre_topc(A_388,B_389))
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ l1_pre_topc(A_388) ) ),
    inference(resolution,[status(thm)],[c_8,c_4474])).

tff(c_4575,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4571])).

tff(c_4581,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4507,c_4507,c_4575])).

tff(c_4971,plain,(
    ! [B_409,A_410] :
      ( v4_tops_1(B_409,A_410)
      | ~ r1_tarski(B_409,k2_pre_topc(A_410,k1_tops_1(A_410,B_409)))
      | ~ r1_tarski(k1_tops_1(A_410,k2_pre_topc(A_410,B_409)),B_409)
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_410)))
      | ~ l1_pre_topc(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4988,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4507,c_4971])).

tff(c_4998,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_6,c_4458,c_4581,c_4988])).

tff(c_5000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4446,c_4998])).

tff(c_5002,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4444])).

tff(c_40,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4445,c_5002,c_4006,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:00:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.14  
% 5.77/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.15  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.77/2.15  
% 5.77/2.15  %Foreground sorts:
% 5.77/2.15  
% 5.77/2.15  
% 5.77/2.15  %Background operators:
% 5.77/2.15  
% 5.77/2.15  
% 5.77/2.15  %Foreground operators:
% 5.77/2.15  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.77/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.15  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 5.77/2.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.77/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.77/2.15  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 5.77/2.15  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.77/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.77/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.77/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.77/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.77/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.77/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.77/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.77/2.15  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.77/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.77/2.15  
% 5.99/2.18  tff(f_129, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_tops_1)).
% 5.99/2.18  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 5.99/2.18  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 5.99/2.18  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.99/2.18  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 5.99/2.18  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 5.99/2.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.99/2.18  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 5.99/2.18  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 5.99/2.18  tff(c_44, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_4017, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 5.99/2.18  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_46, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_53, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 5.99/2.18  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_3392, plain, (![B_277, A_278]: (r1_tarski(B_277, k2_pre_topc(A_278, B_277)) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.99/2.18  tff(c_3396, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_3392])).
% 5.99/2.18  tff(c_3402, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3396])).
% 5.99/2.18  tff(c_782, plain, (![B_120, A_121]: (r1_tarski(B_120, k2_pre_topc(A_121, B_120)) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.99/2.18  tff(c_786, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_782])).
% 5.99/2.18  tff(c_792, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_786])).
% 5.99/2.18  tff(c_64, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 5.99/2.18  tff(c_50, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_54, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 5.99/2.18  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_111, plain, (![A_60, B_61]: (k1_tops_1(A_60, k2_pre_topc(A_60, B_61))=B_61 | ~v6_tops_1(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.99/2.18  tff(c_115, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_111])).
% 5.99/2.18  tff(c_121, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_115])).
% 5.99/2.18  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.99/2.18  tff(c_88, plain, (![A_56, B_57]: (k1_tops_1(A_56, k1_tops_1(A_56, B_57))=k1_tops_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.99/2.18  tff(c_166, plain, (![A_68, B_69]: (k1_tops_1(A_68, k1_tops_1(A_68, k2_pre_topc(A_68, B_69)))=k1_tops_1(A_68, k2_pre_topc(A_68, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_8, c_88])).
% 5.99/2.18  tff(c_170, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_166])).
% 5.99/2.18  tff(c_176, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121, c_121, c_170])).
% 5.99/2.18  tff(c_26, plain, (![C_35, A_23, D_37, B_31]: (v3_pre_topc(C_35, A_23) | k1_tops_1(A_23, C_35)!=C_35 | ~m1_subset_1(D_37, k1_zfmisc_1(u1_struct_0(B_31))) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(B_31) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.99/2.18  tff(c_303, plain, (![D_77, B_78]: (~m1_subset_1(D_77, k1_zfmisc_1(u1_struct_0(B_78))) | ~l1_pre_topc(B_78))), inference(splitLeft, [status(thm)], [c_26])).
% 5.99/2.18  tff(c_306, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_303])).
% 5.99/2.18  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_306])).
% 5.99/2.18  tff(c_315, plain, (![C_79, A_80]: (v3_pre_topc(C_79, A_80) | k1_tops_1(A_80, C_79)!=C_79 | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(splitRight, [status(thm)], [c_26])).
% 5.99/2.18  tff(c_321, plain, (v3_pre_topc('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_315])).
% 5.99/2.18  tff(c_328, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_176, c_321])).
% 5.99/2.18  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_328])).
% 5.99/2.18  tff(c_332, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.99/2.18  tff(c_331, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.99/2.18  tff(c_335, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_331])).
% 5.99/2.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.99/2.18  tff(c_338, plain, (![B_81, A_82]: (r1_tarski(B_81, k2_pre_topc(A_82, B_81)) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.99/2.18  tff(c_340, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_338])).
% 5.99/2.18  tff(c_345, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_340])).
% 5.99/2.18  tff(c_383, plain, (![A_87, B_88]: (k1_tops_1(A_87, k2_pre_topc(A_87, B_88))=B_88 | ~v6_tops_1(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.99/2.18  tff(c_387, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_383])).
% 5.99/2.18  tff(c_393, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_387])).
% 5.99/2.18  tff(c_361, plain, (![A_85, B_86]: (k1_tops_1(A_85, k1_tops_1(A_85, B_86))=k1_tops_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.99/2.18  tff(c_440, plain, (![A_97, B_98]: (k1_tops_1(A_97, k1_tops_1(A_97, k2_pre_topc(A_97, B_98)))=k1_tops_1(A_97, k2_pre_topc(A_97, B_98)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_8, c_361])).
% 5.99/2.18  tff(c_444, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_440])).
% 5.99/2.18  tff(c_450, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_393, c_393, c_444])).
% 5.99/2.18  tff(c_753, plain, (![B_118, A_119]: (v4_tops_1(B_118, A_119) | ~r1_tarski(B_118, k2_pre_topc(A_119, k1_tops_1(A_119, B_118))) | ~r1_tarski(k1_tops_1(A_119, k2_pre_topc(A_119, B_118)), B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.99/2.18  tff(c_767, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_393, c_753])).
% 5.99/2.18  tff(c_775, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_6, c_345, c_450, c_767])).
% 5.99/2.18  tff(c_777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_335, c_775])).
% 5.99/2.18  tff(c_779, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_331])).
% 5.99/2.18  tff(c_42, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_781, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_779, c_42])).
% 5.99/2.18  tff(c_778, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_331])).
% 5.99/2.18  tff(c_28, plain, (![B_31, D_37, C_35, A_23]: (k1_tops_1(B_31, D_37)=D_37 | ~v3_pre_topc(D_37, B_31) | ~m1_subset_1(D_37, k1_zfmisc_1(u1_struct_0(B_31))) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(B_31) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.99/2.18  tff(c_2990, plain, (![C_253, A_254]: (~m1_subset_1(C_253, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254) | ~v2_pre_topc(A_254))), inference(splitLeft, [status(thm)], [c_28])).
% 5.99/2.18  tff(c_3002, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2990])).
% 5.99/2.18  tff(c_3016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3002])).
% 5.99/2.18  tff(c_3018, plain, (![B_255, D_256]: (k1_tops_1(B_255, D_256)=D_256 | ~v3_pre_topc(D_256, B_255) | ~m1_subset_1(D_256, k1_zfmisc_1(u1_struct_0(B_255))) | ~l1_pre_topc(B_255))), inference(splitRight, [status(thm)], [c_28])).
% 5.99/2.18  tff(c_3033, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_3018])).
% 5.99/2.18  tff(c_3046, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_778, c_3033])).
% 5.99/2.18  tff(c_828, plain, (![A_128, B_129]: (k1_tops_1(A_128, k2_pre_topc(A_128, B_129))=B_129 | ~v6_tops_1(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.99/2.18  tff(c_832, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_828])).
% 5.99/2.18  tff(c_838, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_832])).
% 5.99/2.18  tff(c_919, plain, (![A_138, B_139, C_140]: (r1_tarski(k1_tops_1(A_138, B_139), k1_tops_1(A_138, C_140)) | ~r1_tarski(B_139, C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.99/2.18  tff(c_939, plain, (![B_139]: (r1_tarski(k1_tops_1('#skF_1', B_139), '#skF_3') | ~r1_tarski(B_139, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_838, c_919])).
% 5.99/2.18  tff(c_958, plain, (![B_139]: (r1_tarski(k1_tops_1('#skF_1', B_139), '#skF_3') | ~r1_tarski(B_139, k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_939])).
% 5.99/2.18  tff(c_1030, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_958])).
% 5.99/2.18  tff(c_1033, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_1030])).
% 5.99/2.18  tff(c_1037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1033])).
% 5.99/2.18  tff(c_1039, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_958])).
% 5.99/2.18  tff(c_1082, plain, (![C_148, A_149]: (~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149))), inference(splitLeft, [status(thm)], [c_28])).
% 5.99/2.18  tff(c_1085, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1039, c_1082])).
% 5.99/2.18  tff(c_1098, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1085])).
% 5.99/2.18  tff(c_1100, plain, (![B_150, D_151]: (k1_tops_1(B_150, D_151)=D_151 | ~v3_pre_topc(D_151, B_150) | ~m1_subset_1(D_151, k1_zfmisc_1(u1_struct_0(B_150))) | ~l1_pre_topc(B_150))), inference(splitRight, [status(thm)], [c_28])).
% 5.99/2.18  tff(c_1112, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1100])).
% 5.99/2.18  tff(c_1123, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_778, c_1112])).
% 5.99/2.18  tff(c_805, plain, (![A_124, B_125]: (k1_tops_1(A_124, k1_tops_1(A_124, B_125))=k1_tops_1(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.99/2.18  tff(c_811, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_805])).
% 5.99/2.18  tff(c_818, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_811])).
% 5.99/2.18  tff(c_864, plain, (![B_134, A_135]: (r1_tarski(B_134, k2_pre_topc(A_135, k1_tops_1(A_135, B_134))) | ~v4_tops_1(B_134, A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.99/2.18  tff(c_872, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))) | ~v4_tops_1(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_818, c_864])).
% 5.99/2.18  tff(c_880, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))) | ~v4_tops_1(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_872])).
% 5.99/2.18  tff(c_918, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_880])).
% 5.99/2.18  tff(c_1124, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_918])).
% 5.99/2.18  tff(c_1128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1124])).
% 5.99/2.18  tff(c_1130, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_880])).
% 5.99/2.18  tff(c_2805, plain, (![A_242, B_243, C_244]: (r1_tarski(k1_tops_1(A_242, B_243), k1_tops_1(A_242, C_244)) | ~r1_tarski(B_243, C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(u1_struct_0(A_242))) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.99/2.18  tff(c_2828, plain, (![C_244]: (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', C_244)) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_818, c_2805])).
% 5.99/2.18  tff(c_2846, plain, (![C_244]: (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', C_244)) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1130, c_2828])).
% 5.99/2.18  tff(c_3098, plain, (![C_258]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_258)) | ~r1_tarski('#skF_4', C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3046, c_3046, c_2846])).
% 5.99/2.18  tff(c_3105, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_3098])).
% 5.99/2.18  tff(c_3113, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3105])).
% 5.99/2.18  tff(c_855, plain, (![A_132, B_133]: (r1_tarski(k1_tops_1(A_132, k2_pre_topc(A_132, B_133)), B_133) | ~v4_tops_1(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.99/2.18  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.99/2.18  tff(c_3285, plain, (![A_273, B_274]: (k1_tops_1(A_273, k2_pre_topc(A_273, B_274))=B_274 | ~r1_tarski(B_274, k1_tops_1(A_273, k2_pre_topc(A_273, B_274))) | ~v4_tops_1(B_274, A_273) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273))), inference(resolution, [status(thm)], [c_855, c_2])).
% 5.99/2.18  tff(c_3297, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3113, c_3285])).
% 5.99/2.18  tff(c_3313, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_792, c_34, c_781, c_3297])).
% 5.99/2.18  tff(c_18, plain, (![B_13, A_11]: (v6_tops_1(B_13, A_11) | k1_tops_1(A_11, k2_pre_topc(A_11, B_13))!=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.99/2.18  tff(c_3356, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3313, c_18])).
% 5.99/2.18  tff(c_3377, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_3356])).
% 5.99/2.18  tff(c_3379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_3377])).
% 5.99/2.18  tff(c_3381, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 5.99/2.18  tff(c_48, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_3382, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3381, c_48])).
% 5.99/2.18  tff(c_3380, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 5.99/2.18  tff(c_3719, plain, (![C_311, A_312]: (~m1_subset_1(C_311, k1_zfmisc_1(u1_struct_0(A_312))) | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312))), inference(splitLeft, [status(thm)], [c_28])).
% 5.99/2.18  tff(c_3728, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3719])).
% 5.99/2.18  tff(c_3739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3728])).
% 5.99/2.18  tff(c_3741, plain, (![B_313, D_314]: (k1_tops_1(B_313, D_314)=D_314 | ~v3_pre_topc(D_314, B_313) | ~m1_subset_1(D_314, k1_zfmisc_1(u1_struct_0(B_313))) | ~l1_pre_topc(B_313))), inference(splitRight, [status(thm)], [c_28])).
% 5.99/2.18  tff(c_3753, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_3741])).
% 5.99/2.18  tff(c_3763, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3380, c_3753])).
% 5.99/2.18  tff(c_24, plain, (![A_16, B_20, C_22]: (r1_tarski(k1_tops_1(A_16, B_20), k1_tops_1(A_16, C_22)) | ~r1_tarski(B_20, C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.99/2.18  tff(c_3776, plain, (![C_22]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_22)) | ~r1_tarski('#skF_4', C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3763, c_24])).
% 5.99/2.18  tff(c_3793, plain, (![C_315]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_315)) | ~r1_tarski('#skF_4', C_315) | ~m1_subset_1(C_315, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_3776])).
% 5.99/2.18  tff(c_3797, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_3793])).
% 5.99/2.18  tff(c_3803, plain, (![B_4]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', B_4))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3797])).
% 5.99/2.18  tff(c_3456, plain, (![A_289, B_290]: (r1_tarski(k1_tops_1(A_289, k2_pre_topc(A_289, B_290)), B_290) | ~v4_tops_1(B_290, A_289) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_289))) | ~l1_pre_topc(A_289))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.99/2.18  tff(c_3935, plain, (![A_333, B_334]: (k1_tops_1(A_333, k2_pre_topc(A_333, B_334))=B_334 | ~r1_tarski(B_334, k1_tops_1(A_333, k2_pre_topc(A_333, B_334))) | ~v4_tops_1(B_334, A_333) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0(A_333))) | ~l1_pre_topc(A_333))), inference(resolution, [status(thm)], [c_3456, c_2])).
% 5.99/2.18  tff(c_3939, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3803, c_3935])).
% 5.99/2.18  tff(c_3946, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3402, c_34, c_3382, c_3939])).
% 5.99/2.18  tff(c_3979, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3946, c_18])).
% 5.99/2.18  tff(c_4002, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_3979])).
% 5.99/2.18  tff(c_4004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_4002])).
% 5.99/2.18  tff(c_4005, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 5.99/2.18  tff(c_4066, plain, (![A_345, B_346]: (k1_tops_1(A_345, k2_pre_topc(A_345, B_346))=B_346 | ~v6_tops_1(B_346, A_345) | ~m1_subset_1(B_346, k1_zfmisc_1(u1_struct_0(A_345))) | ~l1_pre_topc(A_345))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.99/2.18  tff(c_4070, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4066])).
% 5.99/2.18  tff(c_4076, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4005, c_4070])).
% 5.99/2.18  tff(c_4043, plain, (![A_341, B_342]: (k1_tops_1(A_341, k1_tops_1(A_341, B_342))=k1_tops_1(A_341, B_342) | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.99/2.18  tff(c_4140, plain, (![A_353, B_354]: (k1_tops_1(A_353, k1_tops_1(A_353, k2_pre_topc(A_353, B_354)))=k1_tops_1(A_353, k2_pre_topc(A_353, B_354)) | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0(A_353))) | ~l1_pre_topc(A_353))), inference(resolution, [status(thm)], [c_8, c_4043])).
% 5.99/2.18  tff(c_4144, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4140])).
% 5.99/2.18  tff(c_4150, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4076, c_4076, c_4144])).
% 5.99/2.18  tff(c_4006, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.99/2.18  tff(c_4072, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v6_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_4066])).
% 5.99/2.18  tff(c_4079, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4006, c_4072])).
% 5.99/2.18  tff(c_4178, plain, (![A_355, B_356, C_357]: (r1_tarski(k1_tops_1(A_355, B_356), k1_tops_1(A_355, C_357)) | ~r1_tarski(B_356, C_357) | ~m1_subset_1(C_357, k1_zfmisc_1(u1_struct_0(A_355))) | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0(A_355))) | ~l1_pre_topc(A_355))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.99/2.18  tff(c_4195, plain, (![C_357]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_357)) | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), C_357) | ~m1_subset_1(C_357, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4079, c_4178])).
% 5.99/2.18  tff(c_4215, plain, (![C_357]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_357)) | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), C_357) | ~m1_subset_1(C_357, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4195])).
% 5.99/2.18  tff(c_4295, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_4215])).
% 5.99/2.18  tff(c_4298, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_4295])).
% 5.99/2.18  tff(c_4302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_4298])).
% 5.99/2.18  tff(c_4304, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_4215])).
% 5.99/2.18  tff(c_4364, plain, (![D_366, B_367]: (~m1_subset_1(D_366, k1_zfmisc_1(u1_struct_0(B_367))) | ~l1_pre_topc(B_367))), inference(splitLeft, [status(thm)], [c_26])).
% 5.99/2.18  tff(c_4367, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4304, c_4364])).
% 5.99/2.18  tff(c_4377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_4367])).
% 5.99/2.18  tff(c_4421, plain, (![C_370, A_371]: (v3_pre_topc(C_370, A_371) | k1_tops_1(A_371, C_370)!=C_370 | ~m1_subset_1(C_370, k1_zfmisc_1(u1_struct_0(A_371))) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371))), inference(splitRight, [status(thm)], [c_26])).
% 5.99/2.18  tff(c_4430, plain, (v3_pre_topc('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4421])).
% 5.99/2.18  tff(c_4441, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_4150, c_4430])).
% 5.99/2.18  tff(c_4443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4017, c_4441])).
% 5.99/2.18  tff(c_4445, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.99/2.18  tff(c_4444, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.99/2.18  tff(c_4446, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_4444])).
% 5.99/2.18  tff(c_4451, plain, (![B_372, A_373]: (r1_tarski(B_372, k2_pre_topc(A_373, B_372)) | ~m1_subset_1(B_372, k1_zfmisc_1(u1_struct_0(A_373))) | ~l1_pre_topc(A_373))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.99/2.18  tff(c_4453, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4451])).
% 5.99/2.18  tff(c_4458, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4453])).
% 5.99/2.18  tff(c_4497, plain, (![A_380, B_381]: (k1_tops_1(A_380, k2_pre_topc(A_380, B_381))=B_381 | ~v6_tops_1(B_381, A_380) | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0(A_380))) | ~l1_pre_topc(A_380))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.99/2.18  tff(c_4501, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4497])).
% 5.99/2.18  tff(c_4507, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4005, c_4501])).
% 5.99/2.18  tff(c_4474, plain, (![A_376, B_377]: (k1_tops_1(A_376, k1_tops_1(A_376, B_377))=k1_tops_1(A_376, B_377) | ~m1_subset_1(B_377, k1_zfmisc_1(u1_struct_0(A_376))) | ~l1_pre_topc(A_376))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.99/2.18  tff(c_4571, plain, (![A_388, B_389]: (k1_tops_1(A_388, k1_tops_1(A_388, k2_pre_topc(A_388, B_389)))=k1_tops_1(A_388, k2_pre_topc(A_388, B_389)) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_388))) | ~l1_pre_topc(A_388))), inference(resolution, [status(thm)], [c_8, c_4474])).
% 5.99/2.18  tff(c_4575, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4571])).
% 5.99/2.18  tff(c_4581, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4507, c_4507, c_4575])).
% 5.99/2.18  tff(c_4971, plain, (![B_409, A_410]: (v4_tops_1(B_409, A_410) | ~r1_tarski(B_409, k2_pre_topc(A_410, k1_tops_1(A_410, B_409))) | ~r1_tarski(k1_tops_1(A_410, k2_pre_topc(A_410, B_409)), B_409) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_410))) | ~l1_pre_topc(A_410))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.99/2.18  tff(c_4988, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4507, c_4971])).
% 5.99/2.18  tff(c_4998, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_6, c_4458, c_4581, c_4988])).
% 5.99/2.18  tff(c_5000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4446, c_4998])).
% 5.99/2.18  tff(c_5002, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_4444])).
% 5.99/2.18  tff(c_40, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.99/2.18  tff(c_5006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4445, c_5002, c_4006, c_40])).
% 5.99/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.99/2.18  
% 5.99/2.18  Inference rules
% 5.99/2.18  ----------------------
% 5.99/2.18  #Ref     : 0
% 5.99/2.18  #Sup     : 944
% 5.99/2.18  #Fact    : 0
% 5.99/2.18  #Define  : 0
% 5.99/2.18  #Split   : 111
% 5.99/2.18  #Chain   : 0
% 5.99/2.18  #Close   : 0
% 5.99/2.18  
% 5.99/2.18  Ordering : KBO
% 5.99/2.18  
% 5.99/2.18  Simplification rules
% 5.99/2.18  ----------------------
% 5.99/2.18  #Subsume      : 232
% 5.99/2.18  #Demod        : 1497
% 5.99/2.18  #Tautology    : 363
% 5.99/2.18  #SimpNegUnit  : 20
% 5.99/2.18  #BackRed      : 57
% 5.99/2.18  
% 5.99/2.18  #Partial instantiations: 0
% 5.99/2.18  #Strategies tried      : 1
% 5.99/2.18  
% 5.99/2.18  Timing (in seconds)
% 5.99/2.18  ----------------------
% 5.99/2.18  Preprocessing        : 0.34
% 5.99/2.18  Parsing              : 0.19
% 5.99/2.18  CNF conversion       : 0.02
% 5.99/2.18  Main loop            : 0.99
% 5.99/2.18  Inferencing          : 0.34
% 5.99/2.18  Reduction            : 0.34
% 5.99/2.18  Demodulation         : 0.24
% 5.99/2.18  BG Simplification    : 0.04
% 5.99/2.18  Subsumption          : 0.19
% 5.99/2.18  Abstraction          : 0.05
% 5.99/2.18  MUC search           : 0.00
% 5.99/2.18  Cooper               : 0.00
% 5.99/2.18  Total                : 1.39
% 5.99/2.18  Index Insertion      : 0.00
% 5.99/2.18  Index Deletion       : 0.00
% 5.99/2.18  Index Matching       : 0.00
% 5.99/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
