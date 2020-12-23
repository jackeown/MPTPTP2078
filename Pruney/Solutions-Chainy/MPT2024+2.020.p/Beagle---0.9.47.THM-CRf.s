%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:16 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 474 expanded)
%              Number of leaves         :   31 ( 195 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 (1834 expanded)
%              Number of equality atoms :    8 (  72 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_85,plain,(
    ! [A_84,B_85,C_86] :
      ( '#skF_1'(A_84,B_85,C_86) = C_86
      | ~ m1_subset_1(C_86,u1_struct_0(k9_yellow_6(A_84,B_85)))
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_88,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_94,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_88])).

tff(c_95,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_94])).

tff(c_137,plain,(
    ! [B_104,A_105,C_106] :
      ( r2_hidden(B_104,'#skF_1'(A_105,B_104,C_106))
      | ~ m1_subset_1(C_106,u1_struct_0(k9_yellow_6(A_105,B_104)))
      | ~ m1_subset_1(B_104,u1_struct_0(A_105))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_139,plain,
    ( r2_hidden('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_144,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_95,c_139])).

tff(c_145,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_144])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [B_11,A_65,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_65,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_183,plain,(
    ! [B_112] :
      ( ~ v1_xboole_0(B_112)
      | ~ r1_tarski('#skF_4',B_112) ) ),
    inference(resolution,[status(thm)],[c_145,c_63])).

tff(c_188,plain,(
    ! [B_2] : ~ v1_xboole_0(k2_xboole_0('#skF_4',B_2)) ),
    inference(resolution,[status(thm)],[c_2,c_183])).

tff(c_68,plain,(
    ! [A_69,C_70,B_71] :
      ( m1_subset_1(A_69,C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_69,B_11,A_10] :
      ( m1_subset_1(A_69,B_11)
      | ~ r2_hidden(A_69,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_190,plain,(
    ! [B_114] :
      ( m1_subset_1('#skF_3',B_114)
      | ~ r1_tarski('#skF_4',B_114) ) ),
    inference(resolution,[status(thm)],[c_145,c_71])).

tff(c_195,plain,(
    ! [B_2] : m1_subset_1('#skF_3',k2_xboole_0('#skF_4',B_2)) ),
    inference(resolution,[status(thm)],[c_2,c_190])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_220,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1('#skF_1'(A_118,B_119,C_120),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(C_120,u1_struct_0(k9_yellow_6(A_118,B_119)))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_233,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_220])).

tff(c_241,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_233])).

tff(c_242,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_241])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_283,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_242,c_10])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_91,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_5') = '#skF_5'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_85])).

tff(c_98,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_91])).

tff(c_99,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_98])).

tff(c_230,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_220])).

tff(c_238,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_36,c_230])).

tff(c_239,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_238])).

tff(c_252,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_239,c_10])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k2_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [A_97,B_98,C_99] :
      ( v3_pre_topc('#skF_1'(A_97,B_98,C_99),A_97)
      | ~ m1_subset_1(C_99,u1_struct_0(k9_yellow_6(A_97,B_98)))
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_122,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_127,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_95,c_122])).

tff(c_128,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_127])).

tff(c_124,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_120])).

tff(c_131,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_99,c_124])).

tff(c_132,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_131])).

tff(c_302,plain,(
    ! [B_126,C_127,A_128] :
      ( v3_pre_topc(k2_xboole_0(B_126,C_127),A_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v3_pre_topc(C_127,A_128)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v3_pre_topc(B_126,A_128)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_306,plain,(
    ! [B_126] :
      ( v3_pre_topc(k2_xboole_0(B_126,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_126,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_239,c_302])).

tff(c_348,plain,(
    ! [B_131] :
      ( v3_pre_topc(k2_xboole_0(B_131,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_131,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_132,c_306])).

tff(c_351,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_242,c_348])).

tff(c_365,plain,(
    v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_351])).

tff(c_374,plain,(
    ! [C_132,A_133,B_134] :
      ( r2_hidden(C_132,u1_struct_0(k9_yellow_6(A_133,B_134)))
      | ~ v3_pre_topc(C_132,A_133)
      | ~ r2_hidden(B_134,C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_486,plain,(
    ! [C_159,A_160,B_161] :
      ( m1_subset_1(C_159,u1_struct_0(k9_yellow_6(A_160,B_161)))
      | ~ v3_pre_topc(C_159,A_160)
      | ~ r2_hidden(B_161,C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ m1_subset_1(B_161,u1_struct_0(A_160))
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_374,c_6])).

tff(c_34,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_496,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_486,c_34])).

tff(c_502,plain,
    ( ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_365,c_496])).

tff(c_503,plain,
    ( ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_502])).

tff(c_504,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_508,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_504])).

tff(c_511,plain,
    ( ~ r1_tarski('#skF_5',u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_508])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_252,c_511])).

tff(c_516,plain,(
    ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_520,plain,
    ( v1_xboole_0(k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_8,c_516])).

tff(c_523,plain,(
    v1_xboole_0(k2_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_520])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:58:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.45  
% 3.08/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.46  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.08/1.46  
% 3.08/1.46  %Foreground sorts:
% 3.08/1.46  
% 3.08/1.46  
% 3.08/1.46  %Background operators:
% 3.08/1.46  
% 3.08/1.46  
% 3.08/1.46  %Foreground operators:
% 3.08/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.08/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.08/1.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.08/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.08/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.08/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.46  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 3.08/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.08/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.08/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.46  
% 3.08/1.47  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.08/1.47  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 3.08/1.47  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 3.08/1.47  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.08/1.47  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.08/1.47  tff(f_53, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.08/1.47  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.08/1.47  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.08/1.47  tff(f_74, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 3.08/1.47  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 3.08/1.47  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.08/1.47  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.47  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.47  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.47  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.47  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.47  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.47  tff(c_85, plain, (![A_84, B_85, C_86]: ('#skF_1'(A_84, B_85, C_86)=C_86 | ~m1_subset_1(C_86, u1_struct_0(k9_yellow_6(A_84, B_85))) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.08/1.47  tff(c_88, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_85])).
% 3.08/1.47  tff(c_94, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_88])).
% 3.08/1.47  tff(c_95, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_94])).
% 3.08/1.47  tff(c_137, plain, (![B_104, A_105, C_106]: (r2_hidden(B_104, '#skF_1'(A_105, B_104, C_106)) | ~m1_subset_1(C_106, u1_struct_0(k9_yellow_6(A_105, B_104))) | ~m1_subset_1(B_104, u1_struct_0(A_105)) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.08/1.47  tff(c_139, plain, (r2_hidden('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_137])).
% 3.08/1.47  tff(c_144, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_95, c_139])).
% 3.08/1.47  tff(c_145, plain, (r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_144])).
% 3.08/1.47  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.08/1.47  tff(c_60, plain, (![C_63, B_64, A_65]: (~v1_xboole_0(C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.47  tff(c_63, plain, (![B_11, A_65, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_65, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_60])).
% 3.08/1.47  tff(c_183, plain, (![B_112]: (~v1_xboole_0(B_112) | ~r1_tarski('#skF_4', B_112))), inference(resolution, [status(thm)], [c_145, c_63])).
% 3.08/1.47  tff(c_188, plain, (![B_2]: (~v1_xboole_0(k2_xboole_0('#skF_4', B_2)))), inference(resolution, [status(thm)], [c_2, c_183])).
% 3.08/1.47  tff(c_68, plain, (![A_69, C_70, B_71]: (m1_subset_1(A_69, C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.47  tff(c_71, plain, (![A_69, B_11, A_10]: (m1_subset_1(A_69, B_11) | ~r2_hidden(A_69, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_68])).
% 3.08/1.47  tff(c_190, plain, (![B_114]: (m1_subset_1('#skF_3', B_114) | ~r1_tarski('#skF_4', B_114))), inference(resolution, [status(thm)], [c_145, c_71])).
% 3.08/1.47  tff(c_195, plain, (![B_2]: (m1_subset_1('#skF_3', k2_xboole_0('#skF_4', B_2)))), inference(resolution, [status(thm)], [c_2, c_190])).
% 3.08/1.47  tff(c_8, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.47  tff(c_220, plain, (![A_118, B_119, C_120]: (m1_subset_1('#skF_1'(A_118, B_119, C_120), k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(C_120, u1_struct_0(k9_yellow_6(A_118, B_119))) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.08/1.47  tff(c_233, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_95, c_220])).
% 3.08/1.47  tff(c_241, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_233])).
% 3.08/1.47  tff(c_242, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_241])).
% 3.08/1.47  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.08/1.47  tff(c_283, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_242, c_10])).
% 3.08/1.47  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.47  tff(c_91, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_5')='#skF_5' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_85])).
% 3.08/1.47  tff(c_98, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_5')='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_91])).
% 3.08/1.47  tff(c_99, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_46, c_98])).
% 3.08/1.47  tff(c_230, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_99, c_220])).
% 3.08/1.47  tff(c_238, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_36, c_230])).
% 3.08/1.47  tff(c_239, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_238])).
% 3.08/1.47  tff(c_252, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_239, c_10])).
% 3.08/1.47  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k2_xboole_0(A_3, C_5), B_4) | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.47  tff(c_120, plain, (![A_97, B_98, C_99]: (v3_pre_topc('#skF_1'(A_97, B_98, C_99), A_97) | ~m1_subset_1(C_99, u1_struct_0(k9_yellow_6(A_97, B_98))) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.08/1.47  tff(c_122, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_120])).
% 3.08/1.47  tff(c_127, plain, (v3_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_95, c_122])).
% 3.08/1.47  tff(c_128, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_127])).
% 3.08/1.47  tff(c_124, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_120])).
% 3.08/1.47  tff(c_131, plain, (v3_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_99, c_124])).
% 3.08/1.47  tff(c_132, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_131])).
% 3.08/1.47  tff(c_302, plain, (![B_126, C_127, A_128]: (v3_pre_topc(k2_xboole_0(B_126, C_127), A_128) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~v3_pre_topc(C_127, A_128) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_128))) | ~v3_pre_topc(B_126, A_128) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.08/1.47  tff(c_306, plain, (![B_126]: (v3_pre_topc(k2_xboole_0(B_126, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_126, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_239, c_302])).
% 3.08/1.47  tff(c_348, plain, (![B_131]: (v3_pre_topc(k2_xboole_0(B_131, '#skF_5'), '#skF_2') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_131, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_132, c_306])).
% 3.08/1.47  tff(c_351, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_242, c_348])).
% 3.08/1.47  tff(c_365, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_351])).
% 3.08/1.47  tff(c_374, plain, (![C_132, A_133, B_134]: (r2_hidden(C_132, u1_struct_0(k9_yellow_6(A_133, B_134))) | ~v3_pre_topc(C_132, A_133) | ~r2_hidden(B_134, C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.08/1.47  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.47  tff(c_486, plain, (![C_159, A_160, B_161]: (m1_subset_1(C_159, u1_struct_0(k9_yellow_6(A_160, B_161))) | ~v3_pre_topc(C_159, A_160) | ~r2_hidden(B_161, C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(A_160))) | ~m1_subset_1(B_161, u1_struct_0(A_160)) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_374, c_6])).
% 3.08/1.47  tff(c_34, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.47  tff(c_496, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_486, c_34])).
% 3.08/1.47  tff(c_502, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_365, c_496])).
% 3.08/1.47  tff(c_503, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_502])).
% 3.08/1.47  tff(c_504, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_503])).
% 3.08/1.47  tff(c_508, plain, (~r1_tarski(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_504])).
% 3.08/1.47  tff(c_511, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_508])).
% 3.08/1.47  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_252, c_511])).
% 3.08/1.47  tff(c_516, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_503])).
% 3.08/1.47  tff(c_520, plain, (v1_xboole_0(k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_8, c_516])).
% 3.08/1.47  tff(c_523, plain, (v1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_520])).
% 3.08/1.47  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_523])).
% 3.08/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.47  
% 3.08/1.47  Inference rules
% 3.08/1.47  ----------------------
% 3.08/1.47  #Ref     : 0
% 3.08/1.47  #Sup     : 99
% 3.08/1.47  #Fact    : 0
% 3.08/1.47  #Define  : 0
% 3.08/1.48  #Split   : 3
% 3.08/1.48  #Chain   : 0
% 3.08/1.48  #Close   : 0
% 3.08/1.48  
% 3.08/1.48  Ordering : KBO
% 3.08/1.48  
% 3.08/1.48  Simplification rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Subsume      : 15
% 3.08/1.48  #Demod        : 105
% 3.08/1.48  #Tautology    : 16
% 3.08/1.48  #SimpNegUnit  : 22
% 3.08/1.48  #BackRed      : 0
% 3.08/1.48  
% 3.08/1.48  #Partial instantiations: 0
% 3.08/1.48  #Strategies tried      : 1
% 3.08/1.48  
% 3.08/1.48  Timing (in seconds)
% 3.08/1.48  ----------------------
% 3.21/1.48  Preprocessing        : 0.33
% 3.21/1.48  Parsing              : 0.19
% 3.21/1.48  CNF conversion       : 0.02
% 3.21/1.48  Main loop            : 0.35
% 3.21/1.48  Inferencing          : 0.14
% 3.21/1.48  Reduction            : 0.11
% 3.21/1.48  Demodulation         : 0.07
% 3.21/1.48  BG Simplification    : 0.02
% 3.21/1.48  Subsumption          : 0.06
% 3.21/1.48  Abstraction          : 0.01
% 3.21/1.48  MUC search           : 0.00
% 3.21/1.48  Cooper               : 0.00
% 3.21/1.48  Total                : 0.72
% 3.21/1.48  Index Insertion      : 0.00
% 3.21/1.48  Index Deletion       : 0.00
% 3.21/1.48  Index Matching       : 0.00
% 3.21/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
