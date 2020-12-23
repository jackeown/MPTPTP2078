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
% DateTime   : Thu Dec  3 10:31:10 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 310 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 (1030 expanded)
%              Number of equality atoms :    5 ( 145 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_131,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_98,axiom,(
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
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    ~ v1_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_52,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_51,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_548,plain,(
    ! [A_129,B_130] :
      ( m1_subset_1('#skF_1'(A_129,B_130),k1_zfmisc_1(u1_struct_0(A_129)))
      | v1_tops_2(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129))))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_893,plain,(
    ! [A_161,B_162] :
      ( r1_tarski('#skF_1'(A_161,B_162),u1_struct_0(A_161))
      | v1_tops_2(B_162,A_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161))))
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_548,c_4])).

tff(c_901,plain,
    ( r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_893])).

tff(c_908,plain,
    ( r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_901])).

tff(c_909,plain,(
    r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_908])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_126,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(B_84,u1_pre_topc(A_85))
      | ~ v3_pre_topc(B_84,A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_171,plain,(
    ! [A_88,A_89] :
      ( r2_hidden(A_88,u1_pre_topc(A_89))
      | ~ v3_pre_topc(A_88,A_89)
      | ~ l1_pre_topc(A_89)
      | ~ r1_tarski(A_88,u1_struct_0(A_89)) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1097,plain,(
    ! [A_186,A_187,A_188] :
      ( r2_hidden(A_186,A_187)
      | ~ m1_subset_1(u1_pre_topc(A_188),k1_zfmisc_1(A_187))
      | ~ v3_pre_topc(A_186,A_188)
      | ~ l1_pre_topc(A_188)
      | ~ r1_tarski(A_186,u1_struct_0(A_188)) ) ),
    inference(resolution,[status(thm)],[c_171,c_2])).

tff(c_1110,plain,(
    ! [A_189,B_190,A_191] :
      ( r2_hidden(A_189,B_190)
      | ~ v3_pre_topc(A_189,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ r1_tarski(A_189,u1_struct_0(A_191))
      | ~ r1_tarski(u1_pre_topc(A_191),B_190) ) ),
    inference(resolution,[status(thm)],[c_6,c_1097])).

tff(c_1114,plain,(
    ! [B_190] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4'),B_190)
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(u1_pre_topc('#skF_3'),B_190) ) ),
    inference(resolution,[status(thm)],[c_909,c_1110])).

tff(c_1125,plain,(
    ! [B_190] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4'),B_190)
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
      | ~ r1_tarski(u1_pre_topc('#skF_3'),B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1114])).

tff(c_1133,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1125])).

tff(c_418,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),B_123)
      | v1_tops_2(B_123,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_122))))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_423,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_418])).

tff(c_429,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_423])).

tff(c_430,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_429])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    v1_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_316,plain,(
    ! [B_109,A_110] :
      ( r1_tarski(B_109,u1_pre_topc(A_110))
      | ~ v1_tops_2(B_109,A_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_110))))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_326,plain,
    ( r1_tarski('#skF_4',u1_pre_topc('#skF_2'))
    | ~ v1_tops_2('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_316])).

tff(c_333,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_326])).

tff(c_481,plain,(
    ! [A_127] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4'),A_127)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_127)) ) ),
    inference(resolution,[status(thm)],[c_430,c_2])).

tff(c_77,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,(
    ! [A_67] :
      ( m1_subset_1(A_67,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_77])).

tff(c_219,plain,(
    ! [B_96,A_97] :
      ( v3_pre_topc(B_96,A_97)
      | ~ r2_hidden(B_96,u1_pre_topc(A_97))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_222,plain,(
    ! [A_67] :
      ( v3_pre_topc(A_67,'#skF_2')
      | ~ r2_hidden(A_67,u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_219])).

tff(c_232,plain,(
    ! [A_67] :
      ( v3_pre_topc(A_67,'#skF_2')
      | ~ r2_hidden(A_67,u1_pre_topc('#skF_2'))
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_222])).

tff(c_493,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_481,c_232])).

tff(c_508,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_493])).

tff(c_525,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_508])).

tff(c_528,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_525])).

tff(c_532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_528])).

tff(c_533,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_508])).

tff(c_34,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_202,plain,(
    ! [A_94,B_95] :
      ( m1_pre_topc(A_94,g1_pre_topc(u1_struct_0(B_95),u1_pre_topc(B_95)))
      | ~ m1_pre_topc(A_94,B_95)
      | ~ l1_pre_topc(B_95)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_87,plain,(
    ! [B_70,A_71] :
      ( m1_pre_topc(B_70,A_71)
      | ~ m1_pre_topc(B_70,g1_pre_topc(u1_struct_0(A_71),u1_pre_topc(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    ! [B_70] :
      ( m1_pre_topc(B_70,'#skF_2')
      | ~ m1_pre_topc(B_70,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_96,plain,(
    ! [B_70] :
      ( m1_pre_topc(B_70,'#skF_2')
      | ~ m1_pre_topc(B_70,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_90])).

tff(c_206,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,'#skF_2')
      | ~ m1_pre_topc(A_94,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_202,c_96])).

tff(c_215,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,'#skF_2')
      | ~ m1_pre_topc(A_94,'#skF_3')
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_206])).

tff(c_85,plain,(
    ! [A_67] :
      ( m1_subset_1(A_67,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_51,c_77])).

tff(c_646,plain,(
    ! [D_135,C_136,A_137] :
      ( v3_pre_topc(D_135,C_136)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0(C_136)))
      | ~ v3_pre_topc(D_135,A_137)
      | ~ m1_pre_topc(C_136,A_137)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1212,plain,(
    ! [A_200,A_201] :
      ( v3_pre_topc(A_200,'#skF_3')
      | ~ v3_pre_topc(A_200,A_201)
      | ~ m1_pre_topc('#skF_3',A_201)
      | ~ m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201)
      | ~ r2_hidden(A_200,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_85,c_646])).

tff(c_1222,plain,(
    ! [A_67] :
      ( v3_pre_topc(A_67,'#skF_3')
      | ~ v3_pre_topc(A_67,'#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_86,c_1212])).

tff(c_1237,plain,(
    ! [A_67] :
      ( v3_pre_topc(A_67,'#skF_3')
      | ~ v3_pre_topc(A_67,'#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1222])).

tff(c_1242,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1237])).

tff(c_1245,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_1242])).

tff(c_1248,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1245])).

tff(c_1251,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1248])).

tff(c_1255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1251])).

tff(c_1301,plain,(
    ! [A_205] :
      ( v3_pre_topc(A_205,'#skF_3')
      | ~ v3_pre_topc(A_205,'#skF_2')
      | ~ r2_hidden(A_205,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1237])).

tff(c_1307,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_533,c_1301])).

tff(c_1311,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_1307])).

tff(c_1313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1133,c_1311])).

tff(c_1315,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1125])).

tff(c_22,plain,(
    ! [A_19,B_25] :
      ( ~ v3_pre_topc('#skF_1'(A_19,B_25),A_19)
      | v1_tops_2(B_25,A_19)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19))))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1317,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1315,c_22])).

tff(c_1322,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_51,c_1317])).

tff(c_1324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:13:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.76  
% 3.78/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.76  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.78/1.76  
% 3.78/1.76  %Foreground sorts:
% 3.78/1.76  
% 3.78/1.76  
% 3.78/1.76  %Background operators:
% 3.78/1.76  
% 3.78/1.76  
% 3.78/1.76  %Foreground operators:
% 3.78/1.76  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.78/1.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.78/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.76  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.78/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.76  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.78/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.78/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.76  tff('#skF_5', type, '#skF_5': $i).
% 3.78/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.78/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.78/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.76  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.76  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.78/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.78/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.78/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.76  
% 3.78/1.78  tff(f_131, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v1_tops_2(C, A)) => v1_tops_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_waybel_9)).
% 3.78/1.78  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 3.78/1.78  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.78/1.78  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.78/1.78  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.78/1.78  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 3.78/1.78  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.78/1.78  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.78/1.78  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.78/1.78  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.78/1.78  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 3.78/1.78  tff(c_40, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.78/1.78  tff(c_36, plain, (~v1_tops_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.78/1.78  tff(c_52, plain, (~v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 3.78/1.78  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.78/1.78  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.78/1.78  tff(c_51, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 3.78/1.78  tff(c_548, plain, (![A_129, B_130]: (m1_subset_1('#skF_1'(A_129, B_130), k1_zfmisc_1(u1_struct_0(A_129))) | v1_tops_2(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129)))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.78/1.78  tff(c_4, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.78/1.78  tff(c_893, plain, (![A_161, B_162]: (r1_tarski('#skF_1'(A_161, B_162), u1_struct_0(A_161)) | v1_tops_2(B_162, A_161) | ~m1_subset_1(B_162, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161)))) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_548, c_4])).
% 3.78/1.78  tff(c_901, plain, (r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_51, c_893])).
% 3.78/1.78  tff(c_908, plain, (r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_901])).
% 3.78/1.78  tff(c_909, plain, (r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_908])).
% 3.78/1.78  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.78/1.78  tff(c_126, plain, (![B_84, A_85]: (r2_hidden(B_84, u1_pre_topc(A_85)) | ~v3_pre_topc(B_84, A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.78/1.78  tff(c_171, plain, (![A_88, A_89]: (r2_hidden(A_88, u1_pre_topc(A_89)) | ~v3_pre_topc(A_88, A_89) | ~l1_pre_topc(A_89) | ~r1_tarski(A_88, u1_struct_0(A_89)))), inference(resolution, [status(thm)], [c_6, c_126])).
% 3.78/1.78  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.78  tff(c_1097, plain, (![A_186, A_187, A_188]: (r2_hidden(A_186, A_187) | ~m1_subset_1(u1_pre_topc(A_188), k1_zfmisc_1(A_187)) | ~v3_pre_topc(A_186, A_188) | ~l1_pre_topc(A_188) | ~r1_tarski(A_186, u1_struct_0(A_188)))), inference(resolution, [status(thm)], [c_171, c_2])).
% 3.78/1.78  tff(c_1110, plain, (![A_189, B_190, A_191]: (r2_hidden(A_189, B_190) | ~v3_pre_topc(A_189, A_191) | ~l1_pre_topc(A_191) | ~r1_tarski(A_189, u1_struct_0(A_191)) | ~r1_tarski(u1_pre_topc(A_191), B_190))), inference(resolution, [status(thm)], [c_6, c_1097])).
% 3.78/1.78  tff(c_1114, plain, (![B_190]: (r2_hidden('#skF_1'('#skF_3', '#skF_4'), B_190) | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), B_190))), inference(resolution, [status(thm)], [c_909, c_1110])).
% 3.78/1.78  tff(c_1125, plain, (![B_190]: (r2_hidden('#skF_1'('#skF_3', '#skF_4'), B_190) | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), B_190))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1114])).
% 3.78/1.78  tff(c_1133, plain, (~v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1125])).
% 3.78/1.78  tff(c_418, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), B_123) | v1_tops_2(B_123, A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_122)))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.78/1.78  tff(c_423, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_51, c_418])).
% 3.78/1.78  tff(c_429, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_423])).
% 3.78/1.78  tff(c_430, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_429])).
% 3.78/1.78  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.78/1.78  tff(c_38, plain, (v1_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.78/1.78  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.78/1.78  tff(c_316, plain, (![B_109, A_110]: (r1_tarski(B_109, u1_pre_topc(A_110)) | ~v1_tops_2(B_109, A_110) | ~m1_subset_1(B_109, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_110)))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.78/1.78  tff(c_326, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_2')) | ~v1_tops_2('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_316])).
% 3.78/1.78  tff(c_333, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_326])).
% 3.78/1.78  tff(c_481, plain, (![A_127]: (r2_hidden('#skF_1'('#skF_3', '#skF_4'), A_127) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_127)))), inference(resolution, [status(thm)], [c_430, c_2])).
% 3.78/1.78  tff(c_77, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.78/1.78  tff(c_86, plain, (![A_67]: (m1_subset_1(A_67, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_77])).
% 3.78/1.78  tff(c_219, plain, (![B_96, A_97]: (v3_pre_topc(B_96, A_97) | ~r2_hidden(B_96, u1_pre_topc(A_97)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.78/1.78  tff(c_222, plain, (![A_67]: (v3_pre_topc(A_67, '#skF_2') | ~r2_hidden(A_67, u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_219])).
% 3.78/1.78  tff(c_232, plain, (![A_67]: (v3_pre_topc(A_67, '#skF_2') | ~r2_hidden(A_67, u1_pre_topc('#skF_2')) | ~r2_hidden(A_67, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_222])).
% 3.78/1.78  tff(c_493, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_481, c_232])).
% 3.78/1.78  tff(c_508, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_493])).
% 3.78/1.78  tff(c_525, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_508])).
% 3.78/1.78  tff(c_528, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_525])).
% 3.78/1.78  tff(c_532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_333, c_528])).
% 3.78/1.78  tff(c_533, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_508])).
% 3.78/1.78  tff(c_34, plain, (![A_47]: (m1_pre_topc(A_47, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.78/1.78  tff(c_202, plain, (![A_94, B_95]: (m1_pre_topc(A_94, g1_pre_topc(u1_struct_0(B_95), u1_pre_topc(B_95))) | ~m1_pre_topc(A_94, B_95) | ~l1_pre_topc(B_95) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.78/1.78  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.78/1.78  tff(c_87, plain, (![B_70, A_71]: (m1_pre_topc(B_70, A_71) | ~m1_pre_topc(B_70, g1_pre_topc(u1_struct_0(A_71), u1_pre_topc(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.78/1.78  tff(c_90, plain, (![B_70]: (m1_pre_topc(B_70, '#skF_2') | ~m1_pre_topc(B_70, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_87])).
% 3.78/1.78  tff(c_96, plain, (![B_70]: (m1_pre_topc(B_70, '#skF_2') | ~m1_pre_topc(B_70, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_90])).
% 3.78/1.78  tff(c_206, plain, (![A_94]: (m1_pre_topc(A_94, '#skF_2') | ~m1_pre_topc(A_94, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_202, c_96])).
% 3.78/1.78  tff(c_215, plain, (![A_94]: (m1_pre_topc(A_94, '#skF_2') | ~m1_pre_topc(A_94, '#skF_3') | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_206])).
% 3.78/1.78  tff(c_85, plain, (![A_67]: (m1_subset_1(A_67, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_51, c_77])).
% 3.78/1.78  tff(c_646, plain, (![D_135, C_136, A_137]: (v3_pre_topc(D_135, C_136) | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0(C_136))) | ~v3_pre_topc(D_135, A_137) | ~m1_pre_topc(C_136, A_137) | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.78/1.78  tff(c_1212, plain, (![A_200, A_201]: (v3_pre_topc(A_200, '#skF_3') | ~v3_pre_topc(A_200, A_201) | ~m1_pre_topc('#skF_3', A_201) | ~m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201) | ~r2_hidden(A_200, '#skF_4'))), inference(resolution, [status(thm)], [c_85, c_646])).
% 3.78/1.78  tff(c_1222, plain, (![A_67]: (v3_pre_topc(A_67, '#skF_3') | ~v3_pre_topc(A_67, '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_1212])).
% 3.78/1.78  tff(c_1237, plain, (![A_67]: (v3_pre_topc(A_67, '#skF_3') | ~v3_pre_topc(A_67, '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~r2_hidden(A_67, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1222])).
% 3.78/1.78  tff(c_1242, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1237])).
% 3.78/1.78  tff(c_1245, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_215, c_1242])).
% 3.78/1.78  tff(c_1248, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1245])).
% 3.78/1.78  tff(c_1251, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1248])).
% 3.78/1.78  tff(c_1255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1251])).
% 3.78/1.78  tff(c_1301, plain, (![A_205]: (v3_pre_topc(A_205, '#skF_3') | ~v3_pre_topc(A_205, '#skF_2') | ~r2_hidden(A_205, '#skF_4'))), inference(splitRight, [status(thm)], [c_1237])).
% 3.78/1.78  tff(c_1307, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_533, c_1301])).
% 3.78/1.78  tff(c_1311, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_1307])).
% 3.78/1.78  tff(c_1313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1133, c_1311])).
% 3.78/1.78  tff(c_1315, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_1125])).
% 3.78/1.78  tff(c_22, plain, (![A_19, B_25]: (~v3_pre_topc('#skF_1'(A_19, B_25), A_19) | v1_tops_2(B_25, A_19) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.78/1.78  tff(c_1317, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1315, c_22])).
% 3.78/1.78  tff(c_1322, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_51, c_1317])).
% 3.78/1.78  tff(c_1324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1322])).
% 3.78/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.78  
% 3.78/1.78  Inference rules
% 3.78/1.78  ----------------------
% 3.78/1.78  #Ref     : 0
% 3.78/1.78  #Sup     : 270
% 3.78/1.78  #Fact    : 0
% 3.78/1.78  #Define  : 0
% 3.78/1.78  #Split   : 15
% 3.78/1.78  #Chain   : 0
% 3.78/1.78  #Close   : 0
% 3.78/1.78  
% 3.78/1.78  Ordering : KBO
% 3.78/1.78  
% 3.78/1.78  Simplification rules
% 3.78/1.78  ----------------------
% 3.78/1.78  #Subsume      : 92
% 3.78/1.78  #Demod        : 107
% 3.78/1.78  #Tautology    : 37
% 3.78/1.78  #SimpNegUnit  : 11
% 3.78/1.78  #BackRed      : 0
% 3.78/1.78  
% 3.78/1.78  #Partial instantiations: 0
% 3.78/1.78  #Strategies tried      : 1
% 3.78/1.78  
% 3.78/1.78  Timing (in seconds)
% 3.78/1.78  ----------------------
% 3.78/1.78  Preprocessing        : 0.42
% 3.78/1.78  Parsing              : 0.24
% 3.78/1.78  CNF conversion       : 0.03
% 3.78/1.78  Main loop            : 0.53
% 3.78/1.78  Inferencing          : 0.18
% 3.78/1.78  Reduction            : 0.16
% 3.78/1.78  Demodulation         : 0.10
% 3.78/1.78  BG Simplification    : 0.02
% 3.78/1.78  Subsumption          : 0.12
% 3.78/1.78  Abstraction          : 0.02
% 3.78/1.78  MUC search           : 0.00
% 3.78/1.78  Cooper               : 0.00
% 3.78/1.78  Total                : 0.99
% 3.78/1.78  Index Insertion      : 0.00
% 3.78/1.78  Index Deletion       : 0.00
% 3.78/1.78  Index Matching       : 0.00
% 3.78/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
