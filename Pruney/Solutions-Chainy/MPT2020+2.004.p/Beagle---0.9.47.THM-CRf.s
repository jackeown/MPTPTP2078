%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:10 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 234 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   18
%              Number of atoms          :  176 ( 881 expanded)
%              Number of equality atoms :    5 ( 128 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v1_tops_2(C,A) )
                     => v1_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_9)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_28,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ~ v1_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_39,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    ! [A_42] :
      ( m1_pre_topc(A_42,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_73,plain,(
    ! [A_60,B_61] :
      ( m1_pre_topc(A_60,g1_pre_topc(u1_struct_0(B_61),u1_pre_topc(B_61)))
      | ~ m1_pre_topc(A_60,B_61)
      | ~ l1_pre_topc(B_61)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_55,plain,(
    ! [B_57,A_58] :
      ( m1_pre_topc(B_57,A_58)
      | ~ m1_pre_topc(B_57,g1_pre_topc(u1_struct_0(A_58),u1_pre_topc(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [B_57] :
      ( m1_pre_topc(B_57,'#skF_2')
      | ~ m1_pre_topc(B_57,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_55])).

tff(c_64,plain,(
    ! [B_57] :
      ( m1_pre_topc(B_57,'#skF_2')
      | ~ m1_pre_topc(B_57,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58])).

tff(c_77,plain,(
    ! [A_60] :
      ( m1_pre_topc(A_60,'#skF_2')
      | ~ m1_pre_topc(A_60,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_73,c_64])).

tff(c_89,plain,(
    ! [A_60] :
      ( m1_pre_topc(A_60,'#skF_2')
      | ~ m1_pre_topc(A_60,'#skF_3')
      | ~ l1_pre_topc(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_77])).

tff(c_26,plain,(
    v1_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_175,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1('#skF_1'(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | v1_tops_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73))))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [C_10,A_4,B_8] :
      ( m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(B_8)))
      | ~ m1_pre_topc(B_8,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_178,plain,(
    ! [A_73,B_74,A_4] :
      ( m1_subset_1('#skF_1'(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_pre_topc(A_73,A_4)
      | ~ l1_pre_topc(A_4)
      | v1_tops_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73))))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_175,c_4])).

tff(c_163,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_72)
      | v1_tops_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71))))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_165,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_39,c_163])).

tff(c_170,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_171,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_170])).

tff(c_183,plain,(
    ! [C_78,A_79,B_80] :
      ( v3_pre_topc(C_78,A_79)
      | ~ r2_hidden(C_78,B_80)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ v1_tops_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_194,plain,(
    ! [A_84] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_84)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ v1_tops_2('#skF_4',A_84)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_84))))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_171,c_183])).

tff(c_198,plain,(
    ! [A_4] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_4)
      | ~ v1_tops_2('#skF_4',A_4)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ m1_pre_topc('#skF_3',A_4)
      | ~ l1_pre_topc(A_4)
      | v1_tops_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_178,c_194])).

tff(c_205,plain,(
    ! [A_4] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_4)
      | ~ v1_tops_2('#skF_4',A_4)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ m1_pre_topc('#skF_3',A_4)
      | ~ l1_pre_topc(A_4)
      | v1_tops_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_39,c_198])).

tff(c_211,plain,(
    ! [A_85] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_85)
      | ~ v1_tops_2('#skF_4',A_85)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85))))
      | ~ m1_pre_topc('#skF_3',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_205])).

tff(c_217,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ v1_tops_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_211])).

tff(c_223,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_26,c_217])).

tff(c_224,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_227,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_224])).

tff(c_230,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_227])).

tff(c_233,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_230])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_233])).

tff(c_239,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_238,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_18,plain,(
    ! [A_17,B_23] :
      ( m1_subset_1('#skF_1'(A_17,B_23),k1_zfmisc_1(u1_struct_0(A_17)))
      | v1_tops_2(B_23,A_17)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_179,plain,(
    ! [D_75,C_76,A_77] :
      ( v3_pre_topc(D_75,C_76)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(C_76)))
      | ~ v3_pre_topc(D_75,A_77)
      | ~ m1_pre_topc(C_76,A_77)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_258,plain,(
    ! [A_86,B_87,A_88] :
      ( v3_pre_topc('#skF_1'(A_86,B_87),A_86)
      | ~ v3_pre_topc('#skF_1'(A_86,B_87),A_88)
      | ~ m1_pre_topc(A_86,A_88)
      | ~ m1_subset_1('#skF_1'(A_86,B_87),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | v1_tops_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_86))))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_18,c_179])).

tff(c_265,plain,(
    ! [A_89,B_90,A_91] :
      ( v3_pre_topc('#skF_1'(A_89,B_90),A_89)
      | ~ v3_pre_topc('#skF_1'(A_89,B_90),A_91)
      | ~ m1_pre_topc(A_89,A_91)
      | ~ l1_pre_topc(A_91)
      | v1_tops_2(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_178,c_258])).

tff(c_267,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_238,c_265])).

tff(c_270,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_39,c_38,c_239,c_267])).

tff(c_271,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_270])).

tff(c_14,plain,(
    ! [A_17,B_23] :
      ( ~ v3_pre_topc('#skF_1'(A_17,B_23),A_17)
      | v1_tops_2(B_23,A_17)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_275,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_271,c_14])).

tff(c_282,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_39,c_275])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 12:30:26 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  %$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.21/1.29  
% 2.21/1.29  %Foreground sorts:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Background operators:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Foreground operators:
% 2.21/1.29  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.21/1.29  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.29  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.21/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.29  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.21/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.21/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.29  
% 2.21/1.31  tff(f_113, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v1_tops_2(C, A)) => v1_tops_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_waybel_9)).
% 2.21/1.31  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.21/1.31  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 2.21/1.31  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 2.21/1.31  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 2.21/1.31  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.21/1.31  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 2.21/1.31  tff(c_28, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.31  tff(c_24, plain, (~v1_tops_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.31  tff(c_40, plain, (~v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24])).
% 2.21/1.31  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.31  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.31  tff(c_39, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.21/1.31  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.31  tff(c_22, plain, (![A_42]: (m1_pre_topc(A_42, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.21/1.31  tff(c_73, plain, (![A_60, B_61]: (m1_pre_topc(A_60, g1_pre_topc(u1_struct_0(B_61), u1_pre_topc(B_61))) | ~m1_pre_topc(A_60, B_61) | ~l1_pre_topc(B_61) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.21/1.31  tff(c_30, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.31  tff(c_55, plain, (![B_57, A_58]: (m1_pre_topc(B_57, A_58) | ~m1_pre_topc(B_57, g1_pre_topc(u1_struct_0(A_58), u1_pre_topc(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.31  tff(c_58, plain, (![B_57]: (m1_pre_topc(B_57, '#skF_2') | ~m1_pre_topc(B_57, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_55])).
% 2.21/1.31  tff(c_64, plain, (![B_57]: (m1_pre_topc(B_57, '#skF_2') | ~m1_pre_topc(B_57, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58])).
% 2.21/1.31  tff(c_77, plain, (![A_60]: (m1_pre_topc(A_60, '#skF_2') | ~m1_pre_topc(A_60, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_73, c_64])).
% 2.21/1.31  tff(c_89, plain, (![A_60]: (m1_pre_topc(A_60, '#skF_2') | ~m1_pre_topc(A_60, '#skF_3') | ~l1_pre_topc(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_77])).
% 2.21/1.31  tff(c_26, plain, (v1_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.31  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.31  tff(c_175, plain, (![A_73, B_74]: (m1_subset_1('#skF_1'(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | v1_tops_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73)))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.31  tff(c_4, plain, (![C_10, A_4, B_8]: (m1_subset_1(C_10, k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(C_10, k1_zfmisc_1(u1_struct_0(B_8))) | ~m1_pre_topc(B_8, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.21/1.31  tff(c_178, plain, (![A_73, B_74, A_4]: (m1_subset_1('#skF_1'(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_pre_topc(A_73, A_4) | ~l1_pre_topc(A_4) | v1_tops_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73)))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_175, c_4])).
% 2.21/1.31  tff(c_163, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), B_72) | v1_tops_2(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71)))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.31  tff(c_165, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_39, c_163])).
% 2.21/1.31  tff(c_170, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_165])).
% 2.21/1.31  tff(c_171, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_170])).
% 2.21/1.31  tff(c_183, plain, (![C_78, A_79, B_80]: (v3_pre_topc(C_78, A_79) | ~r2_hidden(C_78, B_80) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~v1_tops_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.31  tff(c_194, plain, (![A_84]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_84) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_84))) | ~v1_tops_2('#skF_4', A_84) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_84)))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_171, c_183])).
% 2.21/1.31  tff(c_198, plain, (![A_4]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_4) | ~v1_tops_2('#skF_4', A_4) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~m1_pre_topc('#skF_3', A_4) | ~l1_pre_topc(A_4) | v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_178, c_194])).
% 2.21/1.31  tff(c_205, plain, (![A_4]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_4) | ~v1_tops_2('#skF_4', A_4) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~m1_pre_topc('#skF_3', A_4) | ~l1_pre_topc(A_4) | v1_tops_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_39, c_198])).
% 2.21/1.31  tff(c_211, plain, (![A_85]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_85) | ~v1_tops_2('#skF_4', A_85) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85)))) | ~m1_pre_topc('#skF_3', A_85) | ~l1_pre_topc(A_85))), inference(negUnitSimplification, [status(thm)], [c_40, c_205])).
% 2.21/1.31  tff(c_217, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~v1_tops_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_211])).
% 2.21/1.31  tff(c_223, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_26, c_217])).
% 2.21/1.31  tff(c_224, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_223])).
% 2.21/1.31  tff(c_227, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_89, c_224])).
% 2.21/1.31  tff(c_230, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_227])).
% 2.21/1.31  tff(c_233, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_230])).
% 2.21/1.31  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_233])).
% 2.21/1.31  tff(c_239, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_223])).
% 2.21/1.31  tff(c_238, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_223])).
% 2.21/1.31  tff(c_18, plain, (![A_17, B_23]: (m1_subset_1('#skF_1'(A_17, B_23), k1_zfmisc_1(u1_struct_0(A_17))) | v1_tops_2(B_23, A_17) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17)))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.31  tff(c_179, plain, (![D_75, C_76, A_77]: (v3_pre_topc(D_75, C_76) | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0(C_76))) | ~v3_pre_topc(D_75, A_77) | ~m1_pre_topc(C_76, A_77) | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.21/1.31  tff(c_258, plain, (![A_86, B_87, A_88]: (v3_pre_topc('#skF_1'(A_86, B_87), A_86) | ~v3_pre_topc('#skF_1'(A_86, B_87), A_88) | ~m1_pre_topc(A_86, A_88) | ~m1_subset_1('#skF_1'(A_86, B_87), k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | v1_tops_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_86)))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_18, c_179])).
% 2.21/1.31  tff(c_265, plain, (![A_89, B_90, A_91]: (v3_pre_topc('#skF_1'(A_89, B_90), A_89) | ~v3_pre_topc('#skF_1'(A_89, B_90), A_91) | ~m1_pre_topc(A_89, A_91) | ~l1_pre_topc(A_91) | v1_tops_2(B_90, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89)))) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_178, c_258])).
% 2.21/1.31  tff(c_267, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_238, c_265])).
% 2.21/1.31  tff(c_270, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_39, c_38, c_239, c_267])).
% 2.21/1.31  tff(c_271, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_270])).
% 2.21/1.31  tff(c_14, plain, (![A_17, B_23]: (~v3_pre_topc('#skF_1'(A_17, B_23), A_17) | v1_tops_2(B_23, A_17) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17)))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.31  tff(c_275, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_271, c_14])).
% 2.21/1.31  tff(c_282, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_39, c_275])).
% 2.21/1.31  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_282])).
% 2.21/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.31  
% 2.21/1.31  Inference rules
% 2.21/1.31  ----------------------
% 2.21/1.31  #Ref     : 0
% 2.21/1.31  #Sup     : 45
% 2.21/1.31  #Fact    : 0
% 2.21/1.31  #Define  : 0
% 2.21/1.31  #Split   : 2
% 2.21/1.31  #Chain   : 0
% 2.21/1.31  #Close   : 0
% 2.21/1.31  
% 2.21/1.31  Ordering : KBO
% 2.21/1.31  
% 2.21/1.31  Simplification rules
% 2.21/1.31  ----------------------
% 2.21/1.31  #Subsume      : 10
% 2.21/1.31  #Demod        : 42
% 2.21/1.31  #Tautology    : 15
% 2.21/1.31  #SimpNegUnit  : 6
% 2.21/1.31  #BackRed      : 0
% 2.21/1.31  
% 2.21/1.31  #Partial instantiations: 0
% 2.21/1.31  #Strategies tried      : 1
% 2.21/1.31  
% 2.21/1.31  Timing (in seconds)
% 2.21/1.31  ----------------------
% 2.21/1.31  Preprocessing        : 0.31
% 2.21/1.31  Parsing              : 0.16
% 2.21/1.31  CNF conversion       : 0.02
% 2.21/1.31  Main loop            : 0.22
% 2.21/1.31  Inferencing          : 0.08
% 2.21/1.31  Reduction            : 0.07
% 2.21/1.31  Demodulation         : 0.05
% 2.21/1.31  BG Simplification    : 0.01
% 2.21/1.31  Subsumption          : 0.05
% 2.21/1.31  Abstraction          : 0.01
% 2.21/1.31  MUC search           : 0.00
% 2.21/1.31  Cooper               : 0.00
% 2.21/1.31  Total                : 0.56
% 2.21/1.31  Index Insertion      : 0.00
% 2.21/1.31  Index Deletion       : 0.00
% 2.21/1.31  Index Matching       : 0.00
% 2.21/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
