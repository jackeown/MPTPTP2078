%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2066+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:50 EST 2020

% Result     : Theorem 15.25s
% Output     : CNFRefutation 15.49s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 534 expanded)
%              Number of leaves         :   33 ( 198 expanded)
%              Depth                    :   21
%              Number of atoms          :  577 (2537 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > v4_pre_topc > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v4_orders_2(C)
                    & v7_waybel_0(C)
                    & v3_yellow_6(C,A)
                    & l1_waybel_0(C,A) )
                 => ( r1_waybel_0(A,C,B)
                   => ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r2_hidden(D,k10_yellow_6(A,C))
                         => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow19)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v2_struct_0(D)
                    & v4_orders_2(D)
                    & v7_waybel_0(D)
                    & v3_yellow_6(D,A)
                    & l1_waybel_0(D,A)
                    & r1_waybel_0(A,D,B)
                    & r2_hidden(C,k10_yellow_6(A,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow19)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(c_64,plain,
    ( ~ v2_struct_0('#skF_5')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_89,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_124,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,k2_pre_topc(A_82,B_81))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_126,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_129,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_126])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_139,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_140,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_pre_topc(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_130,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k2_pre_topc(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [B_34,A_32] :
      ( r1_tarski(B_34,k2_pre_topc(A_32,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_135,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k2_pre_topc(A_83,B_84),k2_pre_topc(A_83,k2_pre_topc(A_83,B_84)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_130,c_32])).

tff(c_199,plain,(
    ! [A_97,B_98] :
      ( r1_tarski(k2_pre_topc(A_97,B_98),k2_pre_topc(A_97,k2_pre_topc(A_97,B_98)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_130,c_32])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [A_78,B_79,B_80] :
      ( r2_hidden('#skF_1'(A_78,B_79),B_80)
      | ~ r1_tarski(A_78,B_80)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_8,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_78,B_79,B_4,B_80] :
      ( r2_hidden('#skF_1'(A_78,B_79),B_4)
      | ~ r1_tarski(B_80,B_4)
      | ~ r1_tarski(A_78,B_80)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_609,plain,(
    ! [A_179,B_180,A_181,B_182] :
      ( r2_hidden('#skF_1'(A_179,B_180),k2_pre_topc(A_181,k2_pre_topc(A_181,B_182)))
      | ~ r1_tarski(A_179,k2_pre_topc(A_181,B_182))
      | r1_tarski(A_179,B_180)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(resolution,[status(thm)],[c_199,c_122])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_633,plain,(
    ! [A_183,A_184,B_185] :
      ( ~ r1_tarski(A_183,k2_pre_topc(A_184,B_185))
      | r1_tarski(A_183,k2_pre_topc(A_184,k2_pre_topc(A_184,B_185)))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_609,c_10])).

tff(c_153,plain,(
    ! [A_87,B_88,B_89,B_90] :
      ( r2_hidden('#skF_1'(A_87,B_88),B_89)
      | ~ r1_tarski(B_90,B_89)
      | ~ r1_tarski(A_87,B_90)
      | r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_160,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),k2_pre_topc('#skF_3','#skF_4'))
      | ~ r1_tarski(A_91,'#skF_4')
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_129,c_153])).

tff(c_245,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(A_107,B_108),B_109)
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_109)
      | ~ r1_tarski(A_107,'#skF_4')
      | r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_160,c_8])).

tff(c_261,plain,(
    ! [B_109,A_107] :
      ( ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_109)
      | ~ r1_tarski(A_107,'#skF_4')
      | r1_tarski(A_107,B_109) ) ),
    inference(resolution,[status(thm)],[c_245,c_10])).

tff(c_676,plain,(
    ! [A_189,A_190,B_191] :
      ( ~ r1_tarski(A_189,'#skF_4')
      | r1_tarski(A_189,k2_pre_topc(A_190,k2_pre_topc(A_190,B_191)))
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc(A_190,B_191))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(resolution,[status(thm)],[c_633,c_261])).

tff(c_685,plain,(
    ! [A_189] :
      ( ~ r1_tarski(A_189,'#skF_4')
      | r1_tarski(A_189,k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_135,c_676])).

tff(c_698,plain,(
    ! [A_189] :
      ( ~ r1_tarski(A_189,'#skF_4')
      | r1_tarski(A_189,k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_685])).

tff(c_705,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_698])).

tff(c_708,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_705])).

tff(c_712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_708])).

tff(c_714,plain,(
    m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_728,plain,
    ( r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_714,c_32])).

tff(c_750,plain,(
    r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_728])).

tff(c_108,plain,(
    ! [A_3,B_4,B_72] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_72)
      | ~ r1_tarski(A_3,B_72)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_34,plain,(
    ! [A_35,C_37,B_36] :
      ( m1_subset_1(A_35,C_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_215,plain,(
    ! [A_99,A_100,B_101] :
      ( m1_subset_1(A_99,u1_struct_0(A_100))
      | ~ r2_hidden(A_99,k2_pre_topc(A_100,B_101))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_130,c_34])).

tff(c_503,plain,(
    ! [A_154,B_155,A_156,B_157] :
      ( m1_subset_1('#skF_1'(A_154,B_155),u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ r1_tarski(A_154,k2_pre_topc(A_156,B_157))
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_108,c_215])).

tff(c_508,plain,(
    ! [A_154,B_155,A_8,B_9] :
      ( m1_subset_1('#skF_1'(A_154,B_155),u1_struct_0(A_8))
      | ~ r1_tarski(A_154,k2_pre_topc(A_8,k2_pre_topc(A_8,B_9)))
      | r1_tarski(A_154,B_155)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_503])).

tff(c_793,plain,(
    ! [B_155] :
      ( m1_subset_1('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_155),u1_struct_0('#skF_3'))
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_155)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_750,c_508])).

tff(c_814,plain,(
    ! [B_155] :
      ( m1_subset_1('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_155),u1_struct_0('#skF_3'))
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_793])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_507,plain,(
    ! [A_154,B_155] :
      ( m1_subset_1('#skF_1'(A_154,B_155),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_40,c_503])).

tff(c_511,plain,(
    ! [A_154,B_155] :
      ( m1_subset_1('#skF_1'(A_154,B_155),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_154,B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_507])).

tff(c_369,plain,(
    ! [A_122,B_123,C_124] :
      ( v4_orders_2('#skF_2'(A_122,B_123,C_124))
      | ~ r2_hidden(C_124,k2_pre_topc(A_122,B_123))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5222,plain,(
    ! [A_437,B_438,A_439,B_440] :
      ( v4_orders_2('#skF_2'(A_437,B_438,'#skF_1'(A_439,B_440)))
      | ~ m1_subset_1('#skF_1'(A_439,B_440),u1_struct_0(A_437))
      | ~ m1_subset_1(B_438,k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437)
      | ~ r1_tarski(A_439,k2_pre_topc(A_437,B_438))
      | r1_tarski(A_439,B_440) ) ),
    inference(resolution,[status(thm)],[c_108,c_369])).

tff(c_5236,plain,(
    ! [B_438,A_154,B_155] :
      ( v4_orders_2('#skF_2'('#skF_3',B_438,'#skF_1'(A_154,B_155)))
      | ~ m1_subset_1(B_438,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3',B_438))
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_511,c_5222])).

tff(c_5267,plain,(
    ! [B_438,A_154,B_155] :
      ( v4_orders_2('#skF_2'('#skF_3',B_438,'#skF_1'(A_154,B_155)))
      | ~ m1_subset_1(B_438,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3',B_438))
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_154,B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5236])).

tff(c_5625,plain,(
    ! [B_503,A_504,B_505] :
      ( v4_orders_2('#skF_2'('#skF_3',B_503,'#skF_1'(A_504,B_505)))
      | ~ m1_subset_1(B_503,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_504,k2_pre_topc('#skF_3',B_503))
      | ~ r1_tarski(A_504,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_504,B_505) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5267])).

tff(c_5643,plain,(
    ! [A_504,B_505] :
      ( v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_1'(A_504,B_505)))
      | ~ r1_tarski(A_504,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_504,B_505) ) ),
    inference(resolution,[status(thm)],[c_40,c_5625])).

tff(c_230,plain,(
    ! [A_104,B_105,C_106] :
      ( v7_waybel_0('#skF_2'(A_104,B_105,C_106))
      | ~ r2_hidden(C_106,k2_pre_topc(A_104,B_105))
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5349,plain,(
    ! [A_457,B_458,A_459,B_460] :
      ( v7_waybel_0('#skF_2'(A_457,B_458,'#skF_1'(A_459,B_460)))
      | ~ m1_subset_1('#skF_1'(A_459,B_460),u1_struct_0(A_457))
      | ~ m1_subset_1(B_458,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457)
      | ~ r1_tarski(A_459,k2_pre_topc(A_457,B_458))
      | r1_tarski(A_459,B_460) ) ),
    inference(resolution,[status(thm)],[c_108,c_230])).

tff(c_5363,plain,(
    ! [B_458,A_154,B_155] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_458,'#skF_1'(A_154,B_155)))
      | ~ m1_subset_1(B_458,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3',B_458))
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_511,c_5349])).

tff(c_5394,plain,(
    ! [B_458,A_154,B_155] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_458,'#skF_1'(A_154,B_155)))
      | ~ m1_subset_1(B_458,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3',B_458))
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_154,B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5363])).

tff(c_5646,plain,(
    ! [B_510,A_511,B_512] :
      ( v7_waybel_0('#skF_2'('#skF_3',B_510,'#skF_1'(A_511,B_512)))
      | ~ m1_subset_1(B_510,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_511,k2_pre_topc('#skF_3',B_510))
      | ~ r1_tarski(A_511,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_511,B_512) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5394])).

tff(c_5664,plain,(
    ! [A_511,B_512] :
      ( v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_511,B_512)))
      | ~ r1_tarski(A_511,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_511,B_512) ) ),
    inference(resolution,[status(thm)],[c_40,c_5646])).

tff(c_522,plain,(
    ! [A_162,B_163,C_164] :
      ( l1_waybel_0('#skF_2'(A_162,B_163,C_164),A_162)
      | ~ r2_hidden(C_164,k2_pre_topc(A_162,B_163))
      | ~ m1_subset_1(C_164,u1_struct_0(A_162))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5458,plain,(
    ! [A_476,B_477,A_478,B_479] :
      ( l1_waybel_0('#skF_2'(A_476,B_477,'#skF_1'(A_478,B_479)),A_476)
      | ~ m1_subset_1('#skF_1'(A_478,B_479),u1_struct_0(A_476))
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0(A_476)))
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476)
      | ~ r1_tarski(A_478,k2_pre_topc(A_476,B_477))
      | r1_tarski(A_478,B_479) ) ),
    inference(resolution,[status(thm)],[c_108,c_522])).

tff(c_5472,plain,(
    ! [B_477,A_154,B_155] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_477,'#skF_1'(A_154,B_155)),'#skF_3')
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3',B_477))
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_511,c_5458])).

tff(c_5503,plain,(
    ! [B_477,A_154,B_155] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_477,'#skF_1'(A_154,B_155)),'#skF_3')
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3',B_477))
      | ~ r1_tarski(A_154,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_154,B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5472])).

tff(c_5694,plain,(
    ! [B_527,A_528,B_529] :
      ( l1_waybel_0('#skF_2'('#skF_3',B_527,'#skF_1'(A_528,B_529)),'#skF_3')
      | ~ m1_subset_1(B_527,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_528,k2_pre_topc('#skF_3',B_527))
      | ~ r1_tarski(A_528,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_528,B_529) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5503])).

tff(c_5712,plain,(
    ! [A_528,B_529] :
      ( l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_528,B_529)),'#skF_3')
      | ~ r1_tarski(A_528,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_528,B_529) ) ),
    inference(resolution,[status(thm)],[c_40,c_5694])).

tff(c_598,plain,(
    ! [A_175,B_176,C_177] :
      ( v3_yellow_6('#skF_2'(A_175,B_176,C_177),A_175)
      | ~ r2_hidden(C_177,k2_pre_topc(A_175,B_176))
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_602,plain,(
    ! [C_177] :
      ( v3_yellow_6('#skF_2'('#skF_3','#skF_4',C_177),'#skF_3')
      | ~ r2_hidden(C_177,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_177,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_598])).

tff(c_606,plain,(
    ! [C_177] :
      ( v3_yellow_6('#skF_2'('#skF_3','#skF_4',C_177),'#skF_3')
      | ~ r2_hidden(C_177,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_177,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_602])).

tff(c_607,plain,(
    ! [C_177] :
      ( v3_yellow_6('#skF_2'('#skF_3','#skF_4',C_177),'#skF_3')
      | ~ r2_hidden(C_177,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_177,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_606])).

tff(c_752,plain,(
    ! [A_192,B_193,C_194] :
      ( r1_waybel_0(A_192,'#skF_2'(A_192,B_193,C_194),B_193)
      | ~ r2_hidden(C_194,k2_pre_topc(A_192,B_193))
      | ~ m1_subset_1(C_194,u1_struct_0(A_192))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_758,plain,(
    ! [C_194] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_194),'#skF_4')
      | ~ r2_hidden(C_194,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_752])).

tff(c_766,plain,(
    ! [C_194] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_194),'#skF_4')
      | ~ r2_hidden(C_194,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_758])).

tff(c_767,plain,(
    ! [C_194] :
      ( r1_waybel_0('#skF_3','#skF_2'('#skF_3','#skF_4',C_194),'#skF_4')
      | ~ r2_hidden(C_194,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_766])).

tff(c_884,plain,(
    ! [C_198,A_199,B_200] :
      ( r2_hidden(C_198,k10_yellow_6(A_199,'#skF_2'(A_199,B_200,C_198)))
      | ~ r2_hidden(C_198,k2_pre_topc(A_199,B_200))
      | ~ m1_subset_1(C_198,u1_struct_0(A_199))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    ! [D_63,C_61] :
      ( v4_pre_topc('#skF_4','#skF_3')
      | r2_hidden(D_63,'#skF_4')
      | ~ r2_hidden(D_63,k10_yellow_6('#skF_3',C_61))
      | ~ m1_subset_1(D_63,u1_struct_0('#skF_3'))
      | ~ r1_waybel_0('#skF_3',C_61,'#skF_4')
      | ~ l1_waybel_0(C_61,'#skF_3')
      | ~ v3_yellow_6(C_61,'#skF_3')
      | ~ v7_waybel_0(C_61)
      | ~ v4_orders_2(C_61)
      | v2_struct_0(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_423,plain,(
    ! [D_63,C_61] :
      ( r2_hidden(D_63,'#skF_4')
      | ~ r2_hidden(D_63,k10_yellow_6('#skF_3',C_61))
      | ~ m1_subset_1(D_63,u1_struct_0('#skF_3'))
      | ~ r1_waybel_0('#skF_3',C_61,'#skF_4')
      | ~ l1_waybel_0(C_61,'#skF_3')
      | ~ v3_yellow_6(C_61,'#skF_3')
      | ~ v7_waybel_0(C_61)
      | ~ v4_orders_2(C_61)
      | v2_struct_0(C_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_86])).

tff(c_888,plain,(
    ! [C_198,B_200] :
      ( r2_hidden(C_198,'#skF_4')
      | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_200,C_198),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_200,C_198),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_200,C_198),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_200,C_198))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_200,C_198))
      | v2_struct_0('#skF_2'('#skF_3',B_200,C_198))
      | ~ r2_hidden(C_198,k2_pre_topc('#skF_3',B_200))
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_884,c_423])).

tff(c_893,plain,(
    ! [C_198,B_200] :
      ( r2_hidden(C_198,'#skF_4')
      | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_200,C_198),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_200,C_198),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_200,C_198),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_200,C_198))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_200,C_198))
      | v2_struct_0('#skF_2'('#skF_3',B_200,C_198))
      | ~ r2_hidden(C_198,k2_pre_topc('#skF_3',B_200))
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_888])).

tff(c_3647,plain,(
    ! [C_355,B_356] :
      ( r2_hidden(C_355,'#skF_4')
      | ~ r1_waybel_0('#skF_3','#skF_2'('#skF_3',B_356,C_355),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3',B_356,C_355),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3',B_356,C_355),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3',B_356,C_355))
      | ~ v4_orders_2('#skF_2'('#skF_3',B_356,C_355))
      | v2_struct_0('#skF_2'('#skF_3',B_356,C_355))
      | ~ r2_hidden(C_355,k2_pre_topc('#skF_3',B_356))
      | ~ m1_subset_1(C_355,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_893])).

tff(c_3649,plain,(
    ! [C_194] :
      ( r2_hidden(C_194,'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4',C_194),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3','#skF_4',C_194),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4',C_194))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4',C_194))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4',C_194))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_194,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_767,c_3647])).

tff(c_5668,plain,(
    ! [C_519] :
      ( r2_hidden(C_519,'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4',C_519),'#skF_3')
      | ~ v3_yellow_6('#skF_2'('#skF_3','#skF_4',C_519),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4',C_519))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4',C_519))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4',C_519))
      | ~ r2_hidden(C_519,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_519,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3649])).

tff(c_8232,plain,(
    ! [C_648] :
      ( r2_hidden(C_648,'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4',C_648),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4',C_648))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4',C_648))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4',C_648))
      | ~ r2_hidden(C_648,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_648,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_607,c_5668])).

tff(c_21630,plain,(
    ! [A_1035,B_1036] :
      ( r2_hidden('#skF_1'(A_1035,B_1036),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1035,B_1036)),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1035,B_1036)))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1035,B_1036)))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1035,B_1036)))
      | ~ m1_subset_1('#skF_1'(A_1035,B_1036),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_1035,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1035,B_1036) ) ),
    inference(resolution,[status(thm)],[c_108,c_8232])).

tff(c_31482,plain,(
    ! [A_1337,B_1338] :
      ( r2_hidden('#skF_1'(A_1337,B_1338),'#skF_4')
      | ~ l1_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1337,B_1338)),'#skF_3')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1337,B_1338)))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1337,B_1338)))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1337,B_1338)))
      | ~ r1_tarski(A_1337,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1337,B_1338) ) ),
    inference(resolution,[status(thm)],[c_511,c_21630])).

tff(c_31575,plain,(
    ! [A_1339,B_1340] :
      ( r2_hidden('#skF_1'(A_1339,B_1340),'#skF_4')
      | ~ v7_waybel_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1339,B_1340)))
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1339,B_1340)))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1339,B_1340)))
      | ~ r1_tarski(A_1339,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1339,B_1340) ) ),
    inference(resolution,[status(thm)],[c_5712,c_31482])).

tff(c_31668,plain,(
    ! [A_1341,B_1342] :
      ( r2_hidden('#skF_1'(A_1341,B_1342),'#skF_4')
      | ~ v4_orders_2('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1341,B_1342)))
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1341,B_1342)))
      | ~ r1_tarski(A_1341,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1341,B_1342) ) ),
    inference(resolution,[status(thm)],[c_5664,c_31575])).

tff(c_31761,plain,(
    ! [A_1343,B_1344] :
      ( r2_hidden('#skF_1'(A_1343,B_1344),'#skF_4')
      | v2_struct_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1343,B_1344)))
      | ~ r1_tarski(A_1343,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1343,B_1344) ) ),
    inference(resolution,[status(thm)],[c_5643,c_31668])).

tff(c_466,plain,(
    ! [A_142,B_143,C_144] :
      ( ~ v2_struct_0('#skF_2'(A_142,B_143,C_144))
      | ~ r2_hidden(C_144,k2_pre_topc(A_142,B_143))
      | ~ m1_subset_1(C_144,u1_struct_0(A_142))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_489,plain,(
    ! [A_142,B_143,A_3,B_4] :
      ( ~ v2_struct_0('#skF_2'(A_142,B_143,'#skF_1'(A_3,B_4)))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0(A_142))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142)
      | ~ r1_tarski(A_3,k2_pre_topc(A_142,B_143))
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_108,c_466])).

tff(c_31768,plain,(
    ! [A_1343,B_1344] :
      ( ~ m1_subset_1('#skF_1'(A_1343,B_1344),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_hidden('#skF_1'(A_1343,B_1344),'#skF_4')
      | ~ r1_tarski(A_1343,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1343,B_1344) ) ),
    inference(resolution,[status(thm)],[c_31761,c_489])).

tff(c_31785,plain,(
    ! [A_1343,B_1344] :
      ( ~ m1_subset_1('#skF_1'(A_1343,B_1344),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r2_hidden('#skF_1'(A_1343,B_1344),'#skF_4')
      | ~ r1_tarski(A_1343,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1343,B_1344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_31768])).

tff(c_31792,plain,(
    ! [A_1345,B_1346] :
      ( ~ m1_subset_1('#skF_1'(A_1345,B_1346),u1_struct_0('#skF_3'))
      | r2_hidden('#skF_1'(A_1345,B_1346),'#skF_4')
      | ~ r1_tarski(A_1345,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1345,B_1346) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_31785])).

tff(c_31813,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_155),'#skF_4')
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_155) ) ),
    inference(resolution,[status(thm)],[c_814,c_31792])).

tff(c_31851,plain,(
    ! [B_1347] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_1347),'#skF_4')
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_1347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31813])).

tff(c_31857,plain,(
    r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_31851,c_10])).

tff(c_31862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_140,c_31857])).

tff(c_31863,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_31892,plain,(
    ! [B_1354,A_1355] :
      ( v4_pre_topc(B_1354,A_1355)
      | k2_pre_topc(A_1355,B_1354) != B_1354
      | ~ v2_pre_topc(A_1355)
      | ~ m1_subset_1(B_1354,k1_zfmisc_1(u1_struct_0(A_1355)))
      | ~ l1_pre_topc(A_1355) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_31898,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_31892])).

tff(c_31902,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_31863,c_31898])).

tff(c_31904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_31902])).

tff(c_31906,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31916,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31906,c_48])).

tff(c_54,plain,
    ( r1_waybel_0('#skF_3','#skF_5','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31918,plain,(
    r1_waybel_0('#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31906,c_54])).

tff(c_31977,plain,(
    ! [A_1375,B_1376] :
      ( k2_pre_topc(A_1375,B_1376) = B_1376
      | ~ v4_pre_topc(B_1376,A_1375)
      | ~ m1_subset_1(B_1376,k1_zfmisc_1(u1_struct_0(A_1375)))
      | ~ l1_pre_topc(A_1375) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_31980,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_31977])).

tff(c_31983,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_31906,c_31980])).

tff(c_31957,plain,(
    ! [B_1370,A_1371] :
      ( r1_tarski(B_1370,k2_pre_topc(A_1371,B_1370))
      | ~ m1_subset_1(B_1370,k1_zfmisc_1(u1_struct_0(A_1371)))
      | ~ l1_pre_topc(A_1371) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_31959,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_31957])).

tff(c_31962,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_31959])).

tff(c_31965,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_31962,c_2])).

tff(c_31966,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_31965])).

tff(c_31984,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31983,c_31966])).

tff(c_31988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31984])).

tff(c_31989,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31965])).

tff(c_31905,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_52,plain,
    ( m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31920,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31906,c_52])).

tff(c_62,plain,
    ( v4_orders_2('#skF_5')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31908,plain,(
    v4_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31906,c_62])).

tff(c_60,plain,
    ( v7_waybel_0('#skF_5')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31910,plain,(
    v7_waybel_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31906,c_60])).

tff(c_58,plain,
    ( v3_yellow_6('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31914,plain,(
    v3_yellow_6('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31906,c_58])).

tff(c_56,plain,
    ( l1_waybel_0('#skF_5','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31912,plain,(
    l1_waybel_0('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31906,c_56])).

tff(c_50,plain,
    ( r2_hidden('#skF_6',k10_yellow_6('#skF_3','#skF_5'))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_31929,plain,(
    r2_hidden('#skF_6',k10_yellow_6('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31906,c_50])).

tff(c_32670,plain,(
    ! [C_1524,A_1525,B_1526,D_1527] :
      ( r2_hidden(C_1524,k2_pre_topc(A_1525,B_1526))
      | ~ r2_hidden(C_1524,k10_yellow_6(A_1525,D_1527))
      | ~ r1_waybel_0(A_1525,D_1527,B_1526)
      | ~ l1_waybel_0(D_1527,A_1525)
      | ~ v3_yellow_6(D_1527,A_1525)
      | ~ v7_waybel_0(D_1527)
      | ~ v4_orders_2(D_1527)
      | v2_struct_0(D_1527)
      | ~ m1_subset_1(C_1524,u1_struct_0(A_1525))
      | ~ m1_subset_1(B_1526,k1_zfmisc_1(u1_struct_0(A_1525)))
      | ~ l1_pre_topc(A_1525)
      | ~ v2_pre_topc(A_1525)
      | v2_struct_0(A_1525) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32680,plain,(
    ! [B_1526] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1526))
      | ~ r1_waybel_0('#skF_3','#skF_5',B_1526)
      | ~ l1_waybel_0('#skF_5','#skF_3')
      | ~ v3_yellow_6('#skF_5','#skF_3')
      | ~ v7_waybel_0('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1526,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_31929,c_32670])).

tff(c_32686,plain,(
    ! [B_1526] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1526))
      | ~ r1_waybel_0('#skF_3','#skF_5',B_1526)
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(B_1526,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_31920,c_31908,c_31910,c_31914,c_31912,c_32680])).

tff(c_32689,plain,(
    ! [B_1529] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1529))
      | ~ r1_waybel_0('#skF_3','#skF_5',B_1529)
      | ~ m1_subset_1(B_1529,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_31905,c_32686])).

tff(c_32696,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_3','#skF_4'))
    | ~ r1_waybel_0('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_32689])).

tff(c_32702,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31918,c_31989,c_32696])).

tff(c_32704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31916,c_32702])).

%------------------------------------------------------------------------------
