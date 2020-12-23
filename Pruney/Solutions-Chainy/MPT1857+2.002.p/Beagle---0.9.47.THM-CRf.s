%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:09 EST 2020

% Result     : Theorem 29.48s
% Output     : CNFRefutation 29.56s
% Verified   : 
% Statistics : Number of formulae       :  135 (1306 expanded)
%              Number of leaves         :   30 ( 457 expanded)
%              Depth                    :   24
%              Number of atoms          :  414 (4485 expanded)
%              Number of equality atoms :   28 ( 619 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v2_tex_2(C,A) )
                     => v2_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26,plain,(
    ! [A_39] :
      ( m1_pre_topc(A_39,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_129,plain,(
    ! [A_93,B_94] :
      ( m1_pre_topc(A_93,g1_pre_topc(u1_struct_0(B_94),u1_pre_topc(B_94)))
      | ~ m1_pre_topc(A_93,B_94)
      | ~ l1_pre_topc(B_94)
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_142,plain,(
    ! [A_93] :
      ( m1_pre_topc(A_93,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_93,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_129])).

tff(c_157,plain,(
    ! [A_96] :
      ( m1_pre_topc(A_96,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_96,'#skF_3')
      | ~ l1_pre_topc(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_142])).

tff(c_16,plain,(
    ! [B_17,A_15] :
      ( m1_pre_topc(B_17,A_15)
      | ~ m1_pre_topc(B_17,g1_pre_topc(u1_struct_0(A_15),u1_pre_topc(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_163,plain,(
    ! [A_96] :
      ( m1_pre_topc(A_96,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(A_96,'#skF_3')
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_157,c_16])).

tff(c_172,plain,(
    ! [A_97] :
      ( m1_pre_topc(A_97,'#skF_4')
      | ~ m1_pre_topc(A_97,'#skF_3')
      | ~ l1_pre_topc(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_163])).

tff(c_179,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_172])).

tff(c_183,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_179])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_381,plain,(
    ! [A_108,B_109] :
      ( r1_tarski('#skF_2'(A_108,B_109),B_109)
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_392,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_381])).

tff(c_402,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_392])).

tff(c_403,plain,(
    r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_402])).

tff(c_111,plain,(
    ! [B_90,A_91] :
      ( m1_pre_topc(B_90,A_91)
      | ~ m1_pre_topc(B_90,g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_114,plain,(
    ! [B_90] :
      ( m1_pre_topc(B_90,'#skF_3')
      | ~ m1_pre_topc(B_90,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_111])).

tff(c_120,plain,(
    ! [B_90] :
      ( m1_pre_topc(B_90,'#skF_3')
      | ~ m1_pre_topc(B_90,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_114])).

tff(c_133,plain,(
    ! [A_93] :
      ( m1_pre_topc(A_93,'#skF_3')
      | ~ m1_pre_topc(A_93,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_129,c_120])).

tff(c_145,plain,(
    ! [A_93] :
      ( m1_pre_topc(A_93,'#skF_3')
      | ~ m1_pre_topc(A_93,'#skF_4')
      | ~ l1_pre_topc(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_133])).

tff(c_102,plain,(
    ! [B_86,A_87] :
      ( m1_subset_1(u1_struct_0(B_86),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [B_86,A_87] :
      ( r1_tarski(u1_struct_0(B_86),u1_struct_0(A_87))
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_107,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(u1_struct_0(B_88),u1_struct_0(A_89))
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [B_98,A_99] :
      ( u1_struct_0(B_98) = u1_struct_0(A_99)
      | ~ r1_tarski(u1_struct_0(A_99),u1_struct_0(B_98))
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_201,plain,(
    ! [B_100,A_101] :
      ( u1_struct_0(B_100) = u1_struct_0(A_101)
      | ~ m1_pre_topc(A_101,B_100)
      | ~ l1_pre_topc(B_100)
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_106,c_190])).

tff(c_203,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_201])).

tff(c_214,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_203])).

tff(c_222,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_225,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_145,c_222])).

tff(c_228,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_225])).

tff(c_245,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_245])).

tff(c_251,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_170,plain,(
    ! [A_96] :
      ( m1_pre_topc(A_96,'#skF_4')
      | ~ m1_pre_topc(A_96,'#skF_3')
      | ~ l1_pre_topc(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_163])).

tff(c_256,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_251,c_170])).

tff(c_265,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_256])).

tff(c_453,plain,(
    ! [C_110,A_111,B_112] :
      ( m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(B_112)))
      | ~ m1_pre_topc(B_112,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_471,plain,(
    ! [A_111] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_pre_topc('#skF_4',A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_48,c_453])).

tff(c_250,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_1766,plain,(
    ! [C_182,A_183] :
      ( m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3',A_183)
      | ~ l1_pre_topc(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_453])).

tff(c_1786,plain,(
    ! [A_183] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_pre_topc('#skF_3',A_183)
      | ~ l1_pre_topc(A_183)
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_471,c_1766])).

tff(c_1817,plain,(
    ! [A_183] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_pre_topc('#skF_3',A_183)
      | ~ l1_pre_topc(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_265,c_1786])).

tff(c_24,plain,(
    ! [B_38,A_36] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_344,plain,(
    ! [B_38] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_38,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_24])).

tff(c_373,plain,(
    ! [B_107] :
      ( m1_subset_1(u1_struct_0(B_107),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_107,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_344])).

tff(c_379,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_373])).

tff(c_412,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_415,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_412])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_183,c_415])).

tff(c_424,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_575,plain,(
    ! [A_120,B_121] :
      ( m1_subset_1('#skF_2'(A_120,B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | v2_tex_2(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2477,plain,(
    ! [A_212,B_213] :
      ( r1_tarski('#skF_2'(A_212,B_213),u1_struct_0(A_212))
      | v2_tex_2(B_213,A_212)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(resolution,[status(thm)],[c_575,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2221,plain,(
    ! [A_203,A_204] :
      ( m1_subset_1(A_203,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ m1_pre_topc('#skF_3',A_204)
      | ~ l1_pre_topc(A_204)
      | ~ r1_tarski(A_203,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1766])).

tff(c_2274,plain,(
    ! [A_203,A_204] :
      ( r1_tarski(A_203,u1_struct_0(A_204))
      | ~ m1_pre_topc('#skF_3',A_204)
      | ~ l1_pre_topc(A_204)
      | ~ r1_tarski(A_203,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2221,c_8])).

tff(c_2480,plain,(
    ! [B_213,A_204] :
      ( r1_tarski('#skF_2'('#skF_4',B_213),u1_struct_0(A_204))
      | ~ m1_pre_topc('#skF_3',A_204)
      | ~ l1_pre_topc(A_204)
      | v2_tex_2(B_213,'#skF_4')
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2477,c_2274])).

tff(c_9252,plain,(
    ! [B_493,A_494] :
      ( r1_tarski('#skF_2'('#skF_4',B_493),u1_struct_0(A_494))
      | ~ m1_pre_topc('#skF_3',A_494)
      | ~ l1_pre_topc(A_494)
      | v2_tex_2(B_493,'#skF_4')
      | ~ m1_subset_1(B_493,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2480])).

tff(c_9274,plain,(
    ! [B_493] :
      ( r1_tarski('#skF_2'('#skF_4',B_493),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_tex_2(B_493,'#skF_4')
      | ~ m1_subset_1(B_493,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_9252])).

tff(c_9288,plain,(
    ! [B_493] :
      ( r1_tarski('#skF_2'('#skF_4',B_493),u1_struct_0('#skF_4'))
      | v2_tex_2(B_493,'#skF_4')
      | ~ m1_subset_1(B_493,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_424,c_9274])).

tff(c_1823,plain,(
    ! [A_3,A_183] :
      ( m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_pre_topc('#skF_3',A_183)
      | ~ l1_pre_topc(A_183)
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1766])).

tff(c_44,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    v2_tex_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_811,plain,(
    ! [A_134,B_135,C_136] :
      ( v3_pre_topc('#skF_1'(A_134,B_135,C_136),A_134)
      | ~ r1_tarski(C_136,B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ v2_tex_2(B_135,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5480,plain,(
    ! [A_328,B_329,A_330] :
      ( v3_pre_topc('#skF_1'(A_328,B_329,A_330),A_328)
      | ~ r1_tarski(A_330,B_329)
      | ~ v2_tex_2(B_329,A_328)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328)
      | ~ r1_tarski(A_330,u1_struct_0(A_328)) ) ),
    inference(resolution,[status(thm)],[c_10,c_811])).

tff(c_5547,plain,(
    ! [A_111,A_330] :
      ( v3_pre_topc('#skF_1'(A_111,'#skF_6',A_330),A_111)
      | ~ r1_tarski(A_330,'#skF_6')
      | ~ v2_tex_2('#skF_6',A_111)
      | ~ r1_tarski(A_330,u1_struct_0(A_111))
      | ~ m1_pre_topc('#skF_4',A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_471,c_5480])).

tff(c_1271,plain,(
    ! [A_159,B_160,C_161] :
      ( m1_subset_1('#skF_1'(A_159,B_160,C_161),k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ r1_tarski(C_161,B_160)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ v2_tex_2(B_160,A_159)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5960,plain,(
    ! [A_349,B_350,C_351] :
      ( r1_tarski('#skF_1'(A_349,B_350,C_351),u1_struct_0(A_349))
      | ~ r1_tarski(C_351,B_350)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ v2_tex_2(B_350,A_349)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_pre_topc(A_349) ) ),
    inference(resolution,[status(thm)],[c_1271,c_8])).

tff(c_5978,plain,(
    ! [B_350,C_351] :
      ( r1_tarski('#skF_1'('#skF_3',B_350,C_351),u1_struct_0('#skF_4'))
      | ~ r1_tarski(C_351,B_350)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_350,'#skF_3')
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_5960])).

tff(c_21008,plain,(
    ! [B_932,C_933] :
      ( r1_tarski('#skF_1'('#skF_3',B_932,C_933),u1_struct_0('#skF_4'))
      | ~ r1_tarski(C_933,B_932)
      | ~ m1_subset_1(C_933,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_932,'#skF_3')
      | ~ m1_subset_1(B_932,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_250,c_250,c_5978])).

tff(c_755,plain,(
    ! [D_128,C_129,A_130] :
      ( v3_pre_topc(D_128,C_129)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0(C_129)))
      | ~ v3_pre_topc(D_128,A_130)
      | ~ m1_pre_topc(C_129,A_130)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2570,plain,(
    ! [A_218,C_219,A_220] :
      ( v3_pre_topc(A_218,C_219)
      | ~ v3_pre_topc(A_218,A_220)
      | ~ m1_pre_topc(C_219,A_220)
      | ~ m1_subset_1(A_218,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220)
      | ~ r1_tarski(A_218,u1_struct_0(C_219)) ) ),
    inference(resolution,[status(thm)],[c_10,c_755])).

tff(c_2578,plain,(
    ! [A_218] :
      ( v3_pre_topc(A_218,'#skF_4')
      | ~ v3_pre_topc(A_218,'#skF_3')
      | ~ m1_subset_1(A_218,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_218,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_251,c_2570])).

tff(c_5564,plain,(
    ! [A_334] :
      ( v3_pre_topc(A_334,'#skF_4')
      | ~ v3_pre_topc(A_334,'#skF_3')
      | ~ m1_subset_1(A_334,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_334,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_250,c_2578])).

tff(c_5698,plain,(
    ! [A_3] :
      ( v3_pre_topc(A_3,'#skF_4')
      | ~ v3_pre_topc(A_3,'#skF_3')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_5564])).

tff(c_59860,plain,(
    ! [B_1853,C_1854] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_1853,C_1854),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_1853,C_1854),'#skF_3')
      | ~ r1_tarski(C_1854,B_1853)
      | ~ m1_subset_1(C_1854,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_1853,'#skF_3')
      | ~ m1_subset_1(B_1853,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_21008,c_5698])).

tff(c_60097,plain,(
    ! [A_330] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_330),'#skF_4')
      | ~ m1_subset_1(A_330,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_330,'#skF_6')
      | ~ v2_tex_2('#skF_6','#skF_3')
      | ~ r1_tarski(A_330,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5547,c_59860])).

tff(c_60605,plain,(
    ! [A_1859] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_1859),'#skF_4')
      | ~ m1_subset_1(A_1859,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_1859,'#skF_6')
      | ~ r1_tarski(A_1859,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_251,c_250,c_56,c_48,c_60097])).

tff(c_60841,plain,(
    ! [A_3] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_3),'#skF_4')
      | ~ r1_tarski(A_3,'#skF_6')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1823,c_60605])).

tff(c_61093,plain,(
    ! [A_1860] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_1860),'#skF_4')
      | ~ r1_tarski(A_1860,'#skF_6')
      | ~ r1_tarski(A_1860,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_183,c_60841])).

tff(c_14,plain,(
    ! [C_14,A_8,B_12] :
      ( m1_subset_1(C_14,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(u1_struct_0(B_12)))
      | ~ m1_pre_topc(B_12,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6750,plain,(
    ! [A_380,B_381,C_382,A_383] :
      ( m1_subset_1('#skF_1'(A_380,B_381,C_382),k1_zfmisc_1(u1_struct_0(A_383)))
      | ~ m1_pre_topc(A_380,A_383)
      | ~ l1_pre_topc(A_383)
      | ~ r1_tarski(C_382,B_381)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ v2_tex_2(B_381,A_380)
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ l1_pre_topc(A_380) ) ),
    inference(resolution,[status(thm)],[c_1271,c_14])).

tff(c_1576,plain,(
    ! [A_176,B_177,C_178] :
      ( k9_subset_1(u1_struct_0(A_176),B_177,'#skF_1'(A_176,B_177,C_178)) = C_178
      | ~ r1_tarski(C_178,B_177)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ v2_tex_2(B_177,A_176)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6135,plain,(
    ! [A_355,B_356,A_357] :
      ( k9_subset_1(u1_struct_0(A_355),B_356,'#skF_1'(A_355,B_356,A_357)) = A_357
      | ~ r1_tarski(A_357,B_356)
      | ~ v2_tex_2(B_356,A_355)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ l1_pre_topc(A_355)
      | ~ r1_tarski(A_357,u1_struct_0(A_355)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1576])).

tff(c_6304,plain,(
    ! [A_360,A_361] :
      ( k9_subset_1(u1_struct_0(A_360),'#skF_6','#skF_1'(A_360,'#skF_6',A_361)) = A_361
      | ~ r1_tarski(A_361,'#skF_6')
      | ~ v2_tex_2('#skF_6',A_360)
      | ~ r1_tarski(A_361,u1_struct_0(A_360))
      | ~ m1_pre_topc('#skF_4',A_360)
      | ~ l1_pre_topc(A_360) ) ),
    inference(resolution,[status(thm)],[c_471,c_6135])).

tff(c_6322,plain,(
    ! [A_361] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_6','#skF_1'('#skF_3','#skF_6',A_361)) = A_361
      | ~ r1_tarski(A_361,'#skF_6')
      | ~ v2_tex_2('#skF_6','#skF_3')
      | ~ r1_tarski(A_361,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_6304])).

tff(c_6333,plain,(
    ! [A_362] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_6','#skF_1'('#skF_3','#skF_6',A_362)) = A_362
      | ~ r1_tarski(A_362,'#skF_6')
      | ~ r1_tarski(A_362,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_251,c_250,c_56,c_6322])).

tff(c_28,plain,(
    ! [A_40,B_54,D_64] :
      ( k9_subset_1(u1_struct_0(A_40),B_54,D_64) != '#skF_2'(A_40,B_54)
      | ~ v3_pre_topc(D_64,A_40)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0(A_40)))
      | v2_tex_2(B_54,A_40)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6341,plain,(
    ! [A_362] :
      ( A_362 != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_362),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_6',A_362),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2('#skF_6','#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_362,'#skF_6')
      | ~ r1_tarski(A_362,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6333,c_28])).

tff(c_6353,plain,(
    ! [A_362] :
      ( A_362 != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_362),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_6',A_362),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2('#skF_6','#skF_4')
      | ~ r1_tarski(A_362,'#skF_6')
      | ~ r1_tarski(A_362,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_6341])).

tff(c_6354,plain,(
    ! [A_362] :
      ( A_362 != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_362),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_6',A_362),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_362,'#skF_6')
      | ~ r1_tarski(A_362,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_6353])).

tff(c_6754,plain,(
    ! [C_382] :
      ( C_382 != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_6',C_382),'#skF_4')
      | ~ r1_tarski(C_382,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(C_382,'#skF_6')
      | ~ m1_subset_1(C_382,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_6','#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6750,c_6354])).

tff(c_8804,plain,(
    ! [C_466] :
      ( C_466 != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_6',C_466),'#skF_4')
      | ~ r1_tarski(C_466,u1_struct_0('#skF_4'))
      | ~ r1_tarski(C_466,'#skF_6')
      | ~ m1_subset_1(C_466,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_250,c_56,c_250,c_52,c_183,c_6754])).

tff(c_8843,plain,(
    ! [A_3] :
      ( A_3 != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_3),'#skF_4')
      | ~ r1_tarski(A_3,'#skF_6')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1823,c_8804])).

tff(c_8924,plain,(
    ! [A_3] :
      ( A_3 != '#skF_2'('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_6',A_3),'#skF_4')
      | ~ r1_tarski(A_3,'#skF_6')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_183,c_8843])).

tff(c_61104,plain,(
    ! [A_1861] :
      ( A_1861 != '#skF_2'('#skF_4','#skF_6')
      | ~ r1_tarski(A_1861,'#skF_6')
      | ~ r1_tarski(A_1861,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_61093,c_8924])).

tff(c_62701,plain,(
    ! [B_1879] :
      ( '#skF_2'('#skF_4',B_1879) != '#skF_2'('#skF_4','#skF_6')
      | ~ r1_tarski('#skF_2'('#skF_4',B_1879),'#skF_6')
      | v2_tex_2(B_1879,'#skF_4')
      | ~ m1_subset_1(B_1879,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_9288,c_61104])).

tff(c_62949,plain,
    ( ~ r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1817,c_62701])).

tff(c_63159,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_183,c_403,c_62949])).

tff(c_63161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_63159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.48/19.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.52/19.43  
% 29.52/19.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.56/19.43  %$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 29.56/19.43  
% 29.56/19.43  %Foreground sorts:
% 29.56/19.43  
% 29.56/19.43  
% 29.56/19.43  %Background operators:
% 29.56/19.43  
% 29.56/19.43  
% 29.56/19.43  %Foreground operators:
% 29.56/19.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 29.56/19.43  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 29.56/19.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 29.56/19.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.56/19.43  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 29.56/19.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 29.56/19.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.56/19.43  tff('#skF_5', type, '#skF_5': $i).
% 29.56/19.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 29.56/19.43  tff('#skF_6', type, '#skF_6': $i).
% 29.56/19.43  tff('#skF_3', type, '#skF_3': $i).
% 29.56/19.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.56/19.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.56/19.43  tff('#skF_4', type, '#skF_4': $i).
% 29.56/19.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.56/19.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 29.56/19.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 29.56/19.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 29.56/19.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 29.56/19.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.56/19.43  
% 29.56/19.45  tff(f_137, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tex_2(C, A)) => v2_tex_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tex_2)).
% 29.56/19.45  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 29.56/19.45  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 29.56/19.45  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 29.56/19.45  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 29.56/19.45  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 29.56/19.45  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 29.56/19.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 29.56/19.45  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 29.56/19.45  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 29.56/19.45  tff(c_40, plain, (~v2_tex_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.56/19.45  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.56/19.45  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.56/19.45  tff(c_26, plain, (![A_39]: (m1_pre_topc(A_39, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_96])).
% 29.56/19.45  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.56/19.45  tff(c_129, plain, (![A_93, B_94]: (m1_pre_topc(A_93, g1_pre_topc(u1_struct_0(B_94), u1_pre_topc(B_94))) | ~m1_pre_topc(A_93, B_94) | ~l1_pre_topc(B_94) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_68])).
% 29.56/19.45  tff(c_142, plain, (![A_93]: (m1_pre_topc(A_93, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_93, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_93))), inference(superposition, [status(thm), theory('equality')], [c_46, c_129])).
% 29.56/19.45  tff(c_157, plain, (![A_96]: (m1_pre_topc(A_96, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_96, '#skF_3') | ~l1_pre_topc(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_142])).
% 29.56/19.45  tff(c_16, plain, (![B_17, A_15]: (m1_pre_topc(B_17, A_15) | ~m1_pre_topc(B_17, g1_pre_topc(u1_struct_0(A_15), u1_pre_topc(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 29.56/19.45  tff(c_163, plain, (![A_96]: (m1_pre_topc(A_96, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(A_96, '#skF_3') | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_157, c_16])).
% 29.56/19.45  tff(c_172, plain, (![A_97]: (m1_pre_topc(A_97, '#skF_4') | ~m1_pre_topc(A_97, '#skF_3') | ~l1_pre_topc(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_163])).
% 29.56/19.45  tff(c_179, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_172])).
% 29.56/19.45  tff(c_183, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_179])).
% 29.56/19.45  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.56/19.45  tff(c_381, plain, (![A_108, B_109]: (r1_tarski('#skF_2'(A_108, B_109), B_109) | v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_117])).
% 29.56/19.45  tff(c_392, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_381])).
% 29.56/19.45  tff(c_402, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_392])).
% 29.56/19.45  tff(c_403, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_402])).
% 29.56/19.45  tff(c_111, plain, (![B_90, A_91]: (m1_pre_topc(B_90, A_91) | ~m1_pre_topc(B_90, g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_59])).
% 29.56/19.45  tff(c_114, plain, (![B_90]: (m1_pre_topc(B_90, '#skF_3') | ~m1_pre_topc(B_90, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_111])).
% 29.56/19.45  tff(c_120, plain, (![B_90]: (m1_pre_topc(B_90, '#skF_3') | ~m1_pre_topc(B_90, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_114])).
% 29.56/19.45  tff(c_133, plain, (![A_93]: (m1_pre_topc(A_93, '#skF_3') | ~m1_pre_topc(A_93, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_129, c_120])).
% 29.56/19.45  tff(c_145, plain, (![A_93]: (m1_pre_topc(A_93, '#skF_3') | ~m1_pre_topc(A_93, '#skF_4') | ~l1_pre_topc(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_133])).
% 29.56/19.45  tff(c_102, plain, (![B_86, A_87]: (m1_subset_1(u1_struct_0(B_86), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.56/19.45  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.56/19.45  tff(c_106, plain, (![B_86, A_87]: (r1_tarski(u1_struct_0(B_86), u1_struct_0(A_87)) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_102, c_8])).
% 29.56/19.45  tff(c_107, plain, (![B_88, A_89]: (r1_tarski(u1_struct_0(B_88), u1_struct_0(A_89)) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_102, c_8])).
% 29.56/19.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.56/19.45  tff(c_190, plain, (![B_98, A_99]: (u1_struct_0(B_98)=u1_struct_0(A_99) | ~r1_tarski(u1_struct_0(A_99), u1_struct_0(B_98)) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_107, c_2])).
% 29.56/19.45  tff(c_201, plain, (![B_100, A_101]: (u1_struct_0(B_100)=u1_struct_0(A_101) | ~m1_pre_topc(A_101, B_100) | ~l1_pre_topc(B_100) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_106, c_190])).
% 29.56/19.45  tff(c_203, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_183, c_201])).
% 29.56/19.45  tff(c_214, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_203])).
% 29.56/19.45  tff(c_222, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_214])).
% 29.56/19.45  tff(c_225, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_145, c_222])).
% 29.56/19.45  tff(c_228, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_225])).
% 29.56/19.45  tff(c_245, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_228])).
% 29.56/19.45  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_245])).
% 29.56/19.45  tff(c_251, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_214])).
% 29.56/19.45  tff(c_170, plain, (![A_96]: (m1_pre_topc(A_96, '#skF_4') | ~m1_pre_topc(A_96, '#skF_3') | ~l1_pre_topc(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_163])).
% 29.56/19.45  tff(c_256, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_251, c_170])).
% 29.56/19.45  tff(c_265, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_256])).
% 29.56/19.45  tff(c_453, plain, (![C_110, A_111, B_112]: (m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_111))) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(B_112))) | ~m1_pre_topc(B_112, A_111) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_52])).
% 29.56/19.45  tff(c_471, plain, (![A_111]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_111))) | ~m1_pre_topc('#skF_4', A_111) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_48, c_453])).
% 29.56/19.45  tff(c_250, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_214])).
% 29.56/19.45  tff(c_1766, plain, (![C_182, A_183]: (m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0(A_183))) | ~m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', A_183) | ~l1_pre_topc(A_183))), inference(superposition, [status(thm), theory('equality')], [c_250, c_453])).
% 29.56/19.45  tff(c_1786, plain, (![A_183]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_183))) | ~m1_pre_topc('#skF_3', A_183) | ~l1_pre_topc(A_183) | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_471, c_1766])).
% 29.56/19.45  tff(c_1817, plain, (![A_183]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_183))) | ~m1_pre_topc('#skF_3', A_183) | ~l1_pre_topc(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_265, c_1786])).
% 29.56/19.45  tff(c_24, plain, (![B_38, A_36]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.56/19.45  tff(c_344, plain, (![B_38]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_38, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_250, c_24])).
% 29.56/19.45  tff(c_373, plain, (![B_107]: (m1_subset_1(u1_struct_0(B_107), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_107, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_344])).
% 29.56/19.45  tff(c_379, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_250, c_373])).
% 29.56/19.45  tff(c_412, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_379])).
% 29.56/19.45  tff(c_415, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_145, c_412])).
% 29.56/19.45  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_183, c_415])).
% 29.56/19.45  tff(c_424, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_379])).
% 29.56/19.45  tff(c_575, plain, (![A_120, B_121]: (m1_subset_1('#skF_2'(A_120, B_121), k1_zfmisc_1(u1_struct_0(A_120))) | v2_tex_2(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_117])).
% 29.56/19.45  tff(c_2477, plain, (![A_212, B_213]: (r1_tarski('#skF_2'(A_212, B_213), u1_struct_0(A_212)) | v2_tex_2(B_213, A_212) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(resolution, [status(thm)], [c_575, c_8])).
% 29.56/19.45  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.56/19.45  tff(c_2221, plain, (![A_203, A_204]: (m1_subset_1(A_203, k1_zfmisc_1(u1_struct_0(A_204))) | ~m1_pre_topc('#skF_3', A_204) | ~l1_pre_topc(A_204) | ~r1_tarski(A_203, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_1766])).
% 29.56/19.45  tff(c_2274, plain, (![A_203, A_204]: (r1_tarski(A_203, u1_struct_0(A_204)) | ~m1_pre_topc('#skF_3', A_204) | ~l1_pre_topc(A_204) | ~r1_tarski(A_203, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2221, c_8])).
% 29.56/19.45  tff(c_2480, plain, (![B_213, A_204]: (r1_tarski('#skF_2'('#skF_4', B_213), u1_struct_0(A_204)) | ~m1_pre_topc('#skF_3', A_204) | ~l1_pre_topc(A_204) | v2_tex_2(B_213, '#skF_4') | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_2477, c_2274])).
% 29.56/19.45  tff(c_9252, plain, (![B_493, A_494]: (r1_tarski('#skF_2'('#skF_4', B_493), u1_struct_0(A_494)) | ~m1_pre_topc('#skF_3', A_494) | ~l1_pre_topc(A_494) | v2_tex_2(B_493, '#skF_4') | ~m1_subset_1(B_493, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2480])).
% 29.56/19.45  tff(c_9274, plain, (![B_493]: (r1_tarski('#skF_2'('#skF_4', B_493), u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_tex_2(B_493, '#skF_4') | ~m1_subset_1(B_493, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_250, c_9252])).
% 29.56/19.45  tff(c_9288, plain, (![B_493]: (r1_tarski('#skF_2'('#skF_4', B_493), u1_struct_0('#skF_4')) | v2_tex_2(B_493, '#skF_4') | ~m1_subset_1(B_493, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_424, c_9274])).
% 29.56/19.45  tff(c_1823, plain, (![A_3, A_183]: (m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_183))) | ~m1_pre_topc('#skF_3', A_183) | ~l1_pre_topc(A_183) | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_1766])).
% 29.56/19.45  tff(c_44, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.56/19.45  tff(c_42, plain, (v2_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 29.56/19.45  tff(c_56, plain, (v2_tex_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 29.56/19.45  tff(c_811, plain, (![A_134, B_135, C_136]: (v3_pre_topc('#skF_1'(A_134, B_135, C_136), A_134) | ~r1_tarski(C_136, B_135) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(A_134))) | ~v2_tex_2(B_135, A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_117])).
% 29.56/19.45  tff(c_5480, plain, (![A_328, B_329, A_330]: (v3_pre_topc('#skF_1'(A_328, B_329, A_330), A_328) | ~r1_tarski(A_330, B_329) | ~v2_tex_2(B_329, A_328) | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328) | ~r1_tarski(A_330, u1_struct_0(A_328)))), inference(resolution, [status(thm)], [c_10, c_811])).
% 29.56/19.45  tff(c_5547, plain, (![A_111, A_330]: (v3_pre_topc('#skF_1'(A_111, '#skF_6', A_330), A_111) | ~r1_tarski(A_330, '#skF_6') | ~v2_tex_2('#skF_6', A_111) | ~r1_tarski(A_330, u1_struct_0(A_111)) | ~m1_pre_topc('#skF_4', A_111) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_471, c_5480])).
% 29.56/19.45  tff(c_1271, plain, (![A_159, B_160, C_161]: (m1_subset_1('#skF_1'(A_159, B_160, C_161), k1_zfmisc_1(u1_struct_0(A_159))) | ~r1_tarski(C_161, B_160) | ~m1_subset_1(C_161, k1_zfmisc_1(u1_struct_0(A_159))) | ~v2_tex_2(B_160, A_159) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_117])).
% 29.56/19.45  tff(c_5960, plain, (![A_349, B_350, C_351]: (r1_tarski('#skF_1'(A_349, B_350, C_351), u1_struct_0(A_349)) | ~r1_tarski(C_351, B_350) | ~m1_subset_1(C_351, k1_zfmisc_1(u1_struct_0(A_349))) | ~v2_tex_2(B_350, A_349) | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_pre_topc(A_349))), inference(resolution, [status(thm)], [c_1271, c_8])).
% 29.56/19.45  tff(c_5978, plain, (![B_350, C_351]: (r1_tarski('#skF_1'('#skF_3', B_350, C_351), u1_struct_0('#skF_4')) | ~r1_tarski(C_351, B_350) | ~m1_subset_1(C_351, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_350, '#skF_3') | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_250, c_5960])).
% 29.56/19.45  tff(c_21008, plain, (![B_932, C_933]: (r1_tarski('#skF_1'('#skF_3', B_932, C_933), u1_struct_0('#skF_4')) | ~r1_tarski(C_933, B_932) | ~m1_subset_1(C_933, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_932, '#skF_3') | ~m1_subset_1(B_932, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_250, c_250, c_5978])).
% 29.56/19.45  tff(c_755, plain, (![D_128, C_129, A_130]: (v3_pre_topc(D_128, C_129) | ~m1_subset_1(D_128, k1_zfmisc_1(u1_struct_0(C_129))) | ~v3_pre_topc(D_128, A_130) | ~m1_pre_topc(C_129, A_130) | ~m1_subset_1(D_128, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_85])).
% 29.56/19.45  tff(c_2570, plain, (![A_218, C_219, A_220]: (v3_pre_topc(A_218, C_219) | ~v3_pre_topc(A_218, A_220) | ~m1_pre_topc(C_219, A_220) | ~m1_subset_1(A_218, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220) | ~r1_tarski(A_218, u1_struct_0(C_219)))), inference(resolution, [status(thm)], [c_10, c_755])).
% 29.56/19.45  tff(c_2578, plain, (![A_218]: (v3_pre_topc(A_218, '#skF_4') | ~v3_pre_topc(A_218, '#skF_3') | ~m1_subset_1(A_218, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_218, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_251, c_2570])).
% 29.56/19.45  tff(c_5564, plain, (![A_334]: (v3_pre_topc(A_334, '#skF_4') | ~v3_pre_topc(A_334, '#skF_3') | ~m1_subset_1(A_334, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_334, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_250, c_2578])).
% 29.56/19.45  tff(c_5698, plain, (![A_3]: (v3_pre_topc(A_3, '#skF_4') | ~v3_pre_topc(A_3, '#skF_3') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_5564])).
% 29.56/19.45  tff(c_59860, plain, (![B_1853, C_1854]: (v3_pre_topc('#skF_1'('#skF_3', B_1853, C_1854), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_1853, C_1854), '#skF_3') | ~r1_tarski(C_1854, B_1853) | ~m1_subset_1(C_1854, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_1853, '#skF_3') | ~m1_subset_1(B_1853, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_21008, c_5698])).
% 29.56/19.45  tff(c_60097, plain, (![A_330]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_330), '#skF_4') | ~m1_subset_1(A_330, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_330, '#skF_6') | ~v2_tex_2('#skF_6', '#skF_3') | ~r1_tarski(A_330, u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_5547, c_59860])).
% 29.56/19.45  tff(c_60605, plain, (![A_1859]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_1859), '#skF_4') | ~m1_subset_1(A_1859, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_1859, '#skF_6') | ~r1_tarski(A_1859, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_251, c_250, c_56, c_48, c_60097])).
% 29.56/19.45  tff(c_60841, plain, (![A_3]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_3), '#skF_4') | ~r1_tarski(A_3, '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1823, c_60605])).
% 29.56/19.45  tff(c_61093, plain, (![A_1860]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_1860), '#skF_4') | ~r1_tarski(A_1860, '#skF_6') | ~r1_tarski(A_1860, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_183, c_60841])).
% 29.56/19.45  tff(c_14, plain, (![C_14, A_8, B_12]: (m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(B_12))) | ~m1_pre_topc(B_12, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 29.56/19.45  tff(c_6750, plain, (![A_380, B_381, C_382, A_383]: (m1_subset_1('#skF_1'(A_380, B_381, C_382), k1_zfmisc_1(u1_struct_0(A_383))) | ~m1_pre_topc(A_380, A_383) | ~l1_pre_topc(A_383) | ~r1_tarski(C_382, B_381) | ~m1_subset_1(C_382, k1_zfmisc_1(u1_struct_0(A_380))) | ~v2_tex_2(B_381, A_380) | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0(A_380))) | ~l1_pre_topc(A_380))), inference(resolution, [status(thm)], [c_1271, c_14])).
% 29.56/19.45  tff(c_1576, plain, (![A_176, B_177, C_178]: (k9_subset_1(u1_struct_0(A_176), B_177, '#skF_1'(A_176, B_177, C_178))=C_178 | ~r1_tarski(C_178, B_177) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_176))) | ~v2_tex_2(B_177, A_176) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_117])).
% 29.56/19.45  tff(c_6135, plain, (![A_355, B_356, A_357]: (k9_subset_1(u1_struct_0(A_355), B_356, '#skF_1'(A_355, B_356, A_357))=A_357 | ~r1_tarski(A_357, B_356) | ~v2_tex_2(B_356, A_355) | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0(A_355))) | ~l1_pre_topc(A_355) | ~r1_tarski(A_357, u1_struct_0(A_355)))), inference(resolution, [status(thm)], [c_10, c_1576])).
% 29.56/19.45  tff(c_6304, plain, (![A_360, A_361]: (k9_subset_1(u1_struct_0(A_360), '#skF_6', '#skF_1'(A_360, '#skF_6', A_361))=A_361 | ~r1_tarski(A_361, '#skF_6') | ~v2_tex_2('#skF_6', A_360) | ~r1_tarski(A_361, u1_struct_0(A_360)) | ~m1_pre_topc('#skF_4', A_360) | ~l1_pre_topc(A_360))), inference(resolution, [status(thm)], [c_471, c_6135])).
% 29.56/19.45  tff(c_6322, plain, (![A_361]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_6', '#skF_1'('#skF_3', '#skF_6', A_361))=A_361 | ~r1_tarski(A_361, '#skF_6') | ~v2_tex_2('#skF_6', '#skF_3') | ~r1_tarski(A_361, u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_250, c_6304])).
% 29.56/19.45  tff(c_6333, plain, (![A_362]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_6', '#skF_1'('#skF_3', '#skF_6', A_362))=A_362 | ~r1_tarski(A_362, '#skF_6') | ~r1_tarski(A_362, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_251, c_250, c_56, c_6322])).
% 29.56/19.45  tff(c_28, plain, (![A_40, B_54, D_64]: (k9_subset_1(u1_struct_0(A_40), B_54, D_64)!='#skF_2'(A_40, B_54) | ~v3_pre_topc(D_64, A_40) | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0(A_40))) | v2_tex_2(B_54, A_40) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_117])).
% 29.56/19.45  tff(c_6341, plain, (![A_362]: (A_362!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_362), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_6', A_362), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_362, '#skF_6') | ~r1_tarski(A_362, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6333, c_28])).
% 29.56/19.45  tff(c_6353, plain, (![A_362]: (A_362!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_362), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_6', A_362), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_6', '#skF_4') | ~r1_tarski(A_362, '#skF_6') | ~r1_tarski(A_362, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_6341])).
% 29.56/19.45  tff(c_6354, plain, (![A_362]: (A_362!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_362), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_6', A_362), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_362, '#skF_6') | ~r1_tarski(A_362, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_40, c_6353])).
% 29.56/19.45  tff(c_6754, plain, (![C_382]: (C_382!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_6', C_382), '#skF_4') | ~r1_tarski(C_382, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(C_382, '#skF_6') | ~m1_subset_1(C_382, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_6', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_6750, c_6354])).
% 29.56/19.45  tff(c_8804, plain, (![C_466]: (C_466!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_6', C_466), '#skF_4') | ~r1_tarski(C_466, u1_struct_0('#skF_4')) | ~r1_tarski(C_466, '#skF_6') | ~m1_subset_1(C_466, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_250, c_56, c_250, c_52, c_183, c_6754])).
% 29.56/19.45  tff(c_8843, plain, (![A_3]: (A_3!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_3), '#skF_4') | ~r1_tarski(A_3, '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1823, c_8804])).
% 29.56/19.45  tff(c_8924, plain, (![A_3]: (A_3!='#skF_2'('#skF_4', '#skF_6') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_6', A_3), '#skF_4') | ~r1_tarski(A_3, '#skF_6') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_183, c_8843])).
% 29.56/19.45  tff(c_61104, plain, (![A_1861]: (A_1861!='#skF_2'('#skF_4', '#skF_6') | ~r1_tarski(A_1861, '#skF_6') | ~r1_tarski(A_1861, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_61093, c_8924])).
% 29.56/19.45  tff(c_62701, plain, (![B_1879]: ('#skF_2'('#skF_4', B_1879)!='#skF_2'('#skF_4', '#skF_6') | ~r1_tarski('#skF_2'('#skF_4', B_1879), '#skF_6') | v2_tex_2(B_1879, '#skF_4') | ~m1_subset_1(B_1879, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_9288, c_61104])).
% 29.56/19.45  tff(c_62949, plain, (~r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1817, c_62701])).
% 29.56/19.45  tff(c_63159, plain, (v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_183, c_403, c_62949])).
% 29.56/19.45  tff(c_63161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_63159])).
% 29.56/19.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.56/19.45  
% 29.56/19.45  Inference rules
% 29.56/19.45  ----------------------
% 29.56/19.45  #Ref     : 0
% 29.56/19.45  #Sup     : 12535
% 29.56/19.45  #Fact    : 0
% 29.56/19.45  #Define  : 0
% 29.56/19.45  #Split   : 29
% 29.56/19.45  #Chain   : 0
% 29.56/19.45  #Close   : 0
% 29.56/19.45  
% 29.56/19.45  Ordering : KBO
% 29.56/19.45  
% 29.56/19.45  Simplification rules
% 29.56/19.45  ----------------------
% 29.56/19.45  #Subsume      : 3142
% 29.56/19.45  #Demod        : 17466
% 29.56/19.45  #Tautology    : 4100
% 29.56/19.45  #SimpNegUnit  : 179
% 29.56/19.45  #BackRed      : 5
% 29.56/19.45  
% 29.56/19.45  #Partial instantiations: 0
% 29.56/19.45  #Strategies tried      : 1
% 29.56/19.45  
% 29.56/19.45  Timing (in seconds)
% 29.56/19.45  ----------------------
% 29.56/19.46  Preprocessing        : 0.35
% 29.56/19.46  Parsing              : 0.17
% 29.56/19.46  CNF conversion       : 0.03
% 29.56/19.46  Main loop            : 18.30
% 29.56/19.46  Inferencing          : 3.64
% 29.56/19.46  Reduction            : 4.60
% 29.56/19.46  Demodulation         : 3.40
% 29.56/19.46  BG Simplification    : 0.23
% 29.56/19.46  Subsumption          : 8.98
% 29.56/19.46  Abstraction          : 0.42
% 29.56/19.46  MUC search           : 0.00
% 29.56/19.46  Cooper               : 0.00
% 29.56/19.46  Total                : 18.71
% 29.56/19.46  Index Insertion      : 0.00
% 29.56/19.46  Index Deletion       : 0.00
% 29.56/19.46  Index Matching       : 0.00
% 29.56/19.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
