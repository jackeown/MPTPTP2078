%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:12 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 391 expanded)
%              Number of leaves         :   29 ( 146 expanded)
%              Depth                    :   10
%              Number of atoms          :  485 (1576 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_83,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_55,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_57,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_54,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_36,plain,(
    ! [D_54] :
      ( ~ r2_hidden('#skF_2',D_54)
      | ~ r1_tarski(D_54,'#skF_3')
      | ~ v3_pre_topc(D_54,'#skF_1')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_357,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_394,plain,(
    ! [B_150,A_151,C_152] :
      ( r1_tarski(B_150,k1_tops_1(A_151,C_152))
      | ~ r1_tarski(B_150,C_152)
      | ~ v3_pre_topc(B_150,A_151)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_403,plain,(
    ! [B_150] :
      ( r1_tarski(B_150,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_150,'#skF_3')
      | ~ v3_pre_topc(B_150,'#skF_1')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_394])).

tff(c_412,plain,(
    ! [B_153] :
      ( r1_tarski(B_153,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_153,'#skF_3')
      | ~ v3_pre_topc(B_153,'#skF_1')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_403])).

tff(c_419,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_412])).

tff(c_432,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_57,c_419])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_68,C_69,B_70] :
      ( m1_subset_1(A_68,C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    ! [A_75,B_76,A_77] :
      ( m1_subset_1(A_75,B_76)
      | ~ r2_hidden(A_75,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_135,plain,(
    ! [B_76] :
      ( m1_subset_1('#skF_2',B_76)
      | ~ r1_tarski('#skF_4',B_76) ) ),
    inference(resolution,[status(thm)],[c_56,c_129])).

tff(c_449,plain,(
    m1_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_432,c_135])).

tff(c_111,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k1_tops_1(A_71,B_72),B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_118,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_111])).

tff(c_125,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_118])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_86,B_87,B_88] :
      ( m1_subset_1(A_86,B_87)
      | ~ r1_tarski(B_88,B_87)
      | v1_xboole_0(B_88)
      | ~ m1_subset_1(A_86,B_88) ) ),
    inference(resolution,[status(thm)],[c_2,c_129])).

tff(c_196,plain,(
    ! [A_86] :
      ( m1_subset_1(A_86,'#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(A_86,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_125,c_181])).

tff(c_228,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_279,plain,(
    ! [B_119,A_120,C_121] :
      ( r1_tarski(B_119,k1_tops_1(A_120,C_121))
      | ~ r1_tarski(B_119,C_121)
      | ~ v3_pre_topc(B_119,A_120)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_288,plain,(
    ! [B_119] :
      ( r1_tarski(B_119,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_119,'#skF_3')
      | ~ v3_pre_topc(B_119,'#skF_1')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_279])).

tff(c_297,plain,(
    ! [B_122] :
      ( r1_tarski(B_122,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_122,'#skF_3')
      | ~ v3_pre_topc(B_122,'#skF_1')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_288])).

tff(c_304,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_297])).

tff(c_317,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_57,c_304])).

tff(c_69,plain,(
    ! [C_61,B_62,A_63] :
      ( ~ v1_xboole_0(C_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_61))
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [B_64,A_65,A_66] :
      ( ~ v1_xboole_0(B_64)
      | ~ r2_hidden(A_65,A_66)
      | ~ r1_tarski(A_66,B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_83,plain,(
    ! [B_64] :
      ( ~ v1_xboole_0(B_64)
      | ~ r1_tarski('#skF_4',B_64) ) ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_329,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_317,c_83])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_329])).

tff(c_341,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_514,plain,(
    ! [C_156,A_157,B_158] :
      ( m1_connsp_2(C_156,A_157,B_158)
      | ~ r2_hidden(B_158,k1_tops_1(A_157,C_156))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_931,plain,(
    ! [C_194,A_195,A_196] :
      ( m1_connsp_2(C_194,A_195,A_196)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(A_196,u1_struct_0(A_195))
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195)
      | v1_xboole_0(k1_tops_1(A_195,C_194))
      | ~ m1_subset_1(A_196,k1_tops_1(A_195,C_194)) ) ),
    inference(resolution,[status(thm)],[c_2,c_514])).

tff(c_940,plain,(
    ! [A_196] :
      ( m1_connsp_2('#skF_3','#skF_1',A_196)
      | ~ m1_subset_1(A_196,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(A_196,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_931])).

tff(c_949,plain,(
    ! [A_196] :
      ( m1_connsp_2('#skF_3','#skF_1',A_196)
      | ~ m1_subset_1(A_196,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1')
      | v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(A_196,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_940])).

tff(c_951,plain,(
    ! [A_197] :
      ( m1_connsp_2('#skF_3','#skF_1',A_197)
      | ~ m1_subset_1(A_197,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(A_197,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_34,c_949])).

tff(c_954,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_449,c_951])).

tff(c_957,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_954])).

tff(c_959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_957])).

tff(c_962,plain,(
    ! [D_198] :
      ( ~ r2_hidden('#skF_2',D_198)
      | ~ r1_tarski(D_198,'#skF_3')
      | ~ v3_pre_topc(D_198,'#skF_1')
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_969,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_962])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_57,c_56,c_969])).

tff(c_984,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_1036,plain,(
    ! [A_215,B_216] :
      ( r1_tarski(k1_tops_1(A_215,B_216),B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1041,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1036])).

tff(c_1045,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1041])).

tff(c_1353,plain,(
    ! [B_277,A_278,C_279] :
      ( r2_hidden(B_277,k1_tops_1(A_278,C_279))
      | ~ m1_connsp_2(C_279,A_278,B_277)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ m1_subset_1(B_277,u1_struct_0(A_278))
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1360,plain,(
    ! [B_277] :
      ( r2_hidden(B_277,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_277)
      | ~ m1_subset_1(B_277,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1353])).

tff(c_1365,plain,(
    ! [B_277] :
      ( r2_hidden(B_277,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_277)
      | ~ m1_subset_1(B_277,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1360])).

tff(c_1367,plain,(
    ! [B_280] :
      ( r2_hidden(B_280,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_280)
      | ~ m1_subset_1(B_280,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1365])).

tff(c_1061,plain,(
    ! [A_219,B_220] :
      ( v3_pre_topc(k1_tops_1(A_219,B_220),A_219)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1067,plain,(
    ! [A_219,A_3] :
      ( v3_pre_topc(k1_tops_1(A_219,A_3),A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | ~ r1_tarski(A_3,u1_struct_0(A_219)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1061])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k1_tops_1(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1110,plain,(
    ! [D_232] :
      ( ~ r2_hidden('#skF_2',D_232)
      | ~ r1_tarski(D_232,'#skF_3')
      | ~ v3_pre_topc(D_232,'#skF_1')
      | ~ m1_subset_1(D_232,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_36])).

tff(c_1114,plain,(
    ! [B_12] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_12))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_12),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_12),'#skF_1')
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_1110])).

tff(c_1161,plain,(
    ! [B_248] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_248))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_248),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_248),'#skF_1')
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1114])).

tff(c_1199,plain,(
    ! [A_255] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_255))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_255),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_255),'#skF_1')
      | ~ r1_tarski(A_255,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1161])).

tff(c_1207,plain,(
    ! [A_3] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_3))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_3),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1067,c_1199])).

tff(c_1216,plain,(
    ! [A_3] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_3))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_3),'#skF_3')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1207])).

tff(c_1373,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1367,c_1216])).

tff(c_1392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_984,c_62,c_1045,c_1373])).

tff(c_1393,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1397,plain,(
    ! [A_283,B_284] :
      ( r1_tarski(A_283,B_284)
      | ~ m1_subset_1(A_283,k1_zfmisc_1(B_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1405,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_1397])).

tff(c_1444,plain,(
    ! [A_305,B_306] :
      ( r1_tarski(k1_tops_1(A_305,B_306),B_306)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1449,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1444])).

tff(c_1453,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1449])).

tff(c_1750,plain,(
    ! [B_370,A_371,C_372] :
      ( r2_hidden(B_370,k1_tops_1(A_371,C_372))
      | ~ m1_connsp_2(C_372,A_371,B_370)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(u1_struct_0(A_371)))
      | ~ m1_subset_1(B_370,u1_struct_0(A_371))
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1757,plain,(
    ! [B_370] :
      ( r2_hidden(B_370,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_370)
      | ~ m1_subset_1(B_370,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1750])).

tff(c_1762,plain,(
    ! [B_370] :
      ( r2_hidden(B_370,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_370)
      | ~ m1_subset_1(B_370,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1757])).

tff(c_1764,plain,(
    ! [B_373] :
      ( r2_hidden(B_373,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_373)
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1762])).

tff(c_1498,plain,(
    ! [A_317,B_318] :
      ( v3_pre_topc(k1_tops_1(A_317,B_318),A_317)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1507,plain,(
    ! [A_317,A_3] :
      ( v3_pre_topc(k1_tops_1(A_317,A_3),A_317)
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317)
      | ~ r1_tarski(A_3,u1_struct_0(A_317)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1498])).

tff(c_1394,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_54] :
      ( ~ r2_hidden('#skF_2',D_54)
      | ~ r1_tarski(D_54,'#skF_3')
      | ~ v3_pre_topc(D_54,'#skF_1')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1512,plain,(
    ! [D_319] :
      ( ~ r2_hidden('#skF_2',D_319)
      | ~ r1_tarski(D_319,'#skF_3')
      | ~ v3_pre_topc(D_319,'#skF_1')
      | ~ m1_subset_1(D_319,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1394,c_44])).

tff(c_1516,plain,(
    ! [B_12] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_12))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_12),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_12),'#skF_1')
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_1512])).

tff(c_1673,plain,(
    ! [B_360] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_360))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_360),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_360),'#skF_1')
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1516])).

tff(c_1696,plain,(
    ! [A_361] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_361))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_361),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_361),'#skF_1')
      | ~ r1_tarski(A_361,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1673])).

tff(c_1704,plain,(
    ! [A_3] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_3))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_3),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1507,c_1696])).

tff(c_1713,plain,(
    ! [A_3] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_3))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_3),'#skF_3')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1704])).

tff(c_1768,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1764,c_1713])).

tff(c_1785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1393,c_1405,c_1453,c_1768])).

tff(c_1786,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1790,plain,(
    ! [A_376,B_377] :
      ( r1_tarski(A_376,B_377)
      | ~ m1_subset_1(A_376,k1_zfmisc_1(B_377)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1798,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_1790])).

tff(c_1834,plain,(
    ! [A_396,B_397] :
      ( r1_tarski(k1_tops_1(A_396,B_397),B_397)
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ l1_pre_topc(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1839,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1834])).

tff(c_1843,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1839])).

tff(c_2393,plain,(
    ! [B_511,A_512,C_513] :
      ( r2_hidden(B_511,k1_tops_1(A_512,C_513))
      | ~ m1_connsp_2(C_513,A_512,B_511)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(u1_struct_0(A_512)))
      | ~ m1_subset_1(B_511,u1_struct_0(A_512))
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2400,plain,(
    ! [B_511] :
      ( r2_hidden(B_511,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_511)
      | ~ m1_subset_1(B_511,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_2393])).

tff(c_2405,plain,(
    ! [B_511] :
      ( r2_hidden(B_511,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_511)
      | ~ m1_subset_1(B_511,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2400])).

tff(c_2407,plain,(
    ! [B_514] :
      ( r2_hidden(B_514,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_514)
      | ~ m1_subset_1(B_514,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2405])).

tff(c_2185,plain,(
    ! [A_460,B_461] :
      ( v3_pre_topc(k1_tops_1(A_460,B_461),A_460)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(u1_struct_0(A_460)))
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2194,plain,(
    ! [A_460,A_3] :
      ( v3_pre_topc(k1_tops_1(A_460,A_3),A_460)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | ~ r1_tarski(A_3,u1_struct_0(A_460)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2185])).

tff(c_2140,plain,(
    ! [A_455,B_456] :
      ( m1_subset_1(k1_tops_1(A_455,B_456),k1_zfmisc_1(u1_struct_0(A_455)))
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0(A_455)))
      | ~ l1_pre_topc(A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1787,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [D_54] :
      ( ~ r2_hidden('#skF_2',D_54)
      | ~ r1_tarski(D_54,'#skF_3')
      | ~ v3_pre_topc(D_54,'#skF_1')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1861,plain,(
    ! [D_54] :
      ( ~ r2_hidden('#skF_2',D_54)
      | ~ r1_tarski(D_54,'#skF_3')
      | ~ v3_pre_topc(D_54,'#skF_1')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1787,c_40])).

tff(c_2144,plain,(
    ! [B_456] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_456))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_456),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_456),'#skF_1')
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2140,c_1861])).

tff(c_2315,plain,(
    ! [B_501] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_501))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_501),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_501),'#skF_1')
      | ~ m1_subset_1(B_501,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2144])).

tff(c_2339,plain,(
    ! [A_502] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_502))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_502),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_502),'#skF_1')
      | ~ r1_tarski(A_502,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_2315])).

tff(c_2347,plain,(
    ! [A_3] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_3))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_3),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2194,c_2339])).

tff(c_2356,plain,(
    ! [A_3] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_3))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_3),'#skF_3')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2347])).

tff(c_2411,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2407,c_2356])).

tff(c_2428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1786,c_1798,c_1843,c_2411])).

tff(c_2429,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2434,plain,(
    ! [A_517,B_518] :
      ( r1_tarski(A_517,B_518)
      | ~ m1_subset_1(A_517,k1_zfmisc_1(B_518)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2442,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_2434])).

tff(c_2477,plain,(
    ! [A_540,B_541] :
      ( r1_tarski(k1_tops_1(A_540,B_541),B_541)
      | ~ m1_subset_1(B_541,k1_zfmisc_1(u1_struct_0(A_540)))
      | ~ l1_pre_topc(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2482,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2477])).

tff(c_2486,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2482])).

tff(c_3367,plain,(
    ! [B_709,A_710,C_711] :
      ( r2_hidden(B_709,k1_tops_1(A_710,C_711))
      | ~ m1_connsp_2(C_711,A_710,B_709)
      | ~ m1_subset_1(C_711,k1_zfmisc_1(u1_struct_0(A_710)))
      | ~ m1_subset_1(B_709,u1_struct_0(A_710))
      | ~ l1_pre_topc(A_710)
      | ~ v2_pre_topc(A_710)
      | v2_struct_0(A_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3374,plain,(
    ! [B_709] :
      ( r2_hidden(B_709,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_3367])).

tff(c_3379,plain,(
    ! [B_709] :
      ( r2_hidden(B_709,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3374])).

tff(c_3381,plain,(
    ! [B_712] :
      ( r2_hidden(B_712,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_712)
      | ~ m1_subset_1(B_712,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3379])).

tff(c_2785,plain,(
    ! [A_598,B_599] :
      ( v3_pre_topc(k1_tops_1(A_598,B_599),A_598)
      | ~ m1_subset_1(B_599,k1_zfmisc_1(u1_struct_0(A_598)))
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2791,plain,(
    ! [A_598,A_3] :
      ( v3_pre_topc(k1_tops_1(A_598,A_3),A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | ~ r1_tarski(A_3,u1_struct_0(A_598)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2785])).

tff(c_3144,plain,(
    ! [A_669,B_670] :
      ( m1_subset_1(k1_tops_1(A_669,B_670),k1_zfmisc_1(u1_struct_0(A_669)))
      | ~ m1_subset_1(B_670,k1_zfmisc_1(u1_struct_0(A_669)))
      | ~ l1_pre_topc(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2430,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_54] :
      ( ~ r2_hidden('#skF_2',D_54)
      | ~ r1_tarski(D_54,'#skF_3')
      | ~ v3_pre_topc(D_54,'#skF_1')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3120,plain,(
    ! [D_54] :
      ( ~ r2_hidden('#skF_2',D_54)
      | ~ r1_tarski(D_54,'#skF_3')
      | ~ v3_pre_topc(D_54,'#skF_1')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2430,c_48])).

tff(c_3148,plain,(
    ! [B_670] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_670))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_670),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_670),'#skF_1')
      | ~ m1_subset_1(B_670,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3144,c_3120])).

tff(c_3225,plain,(
    ! [B_698] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_698))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_698),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_698),'#skF_1')
      | ~ m1_subset_1(B_698,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3148])).

tff(c_3249,plain,(
    ! [A_699] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_699))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_699),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_699),'#skF_1')
      | ~ r1_tarski(A_699,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3225])).

tff(c_3257,plain,(
    ! [A_3] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_3))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_3),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2791,c_3249])).

tff(c_3266,plain,(
    ! [A_3] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_3))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_3),'#skF_3')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3257])).

tff(c_3385,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3381,c_3266])).

tff(c_3400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2429,c_2442,c_2486,c_3385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n025.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 14:28:20 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.15  
% 5.75/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.15  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.75/2.15  
% 5.75/2.15  %Foreground sorts:
% 5.75/2.15  
% 5.75/2.15  
% 5.75/2.15  %Background operators:
% 5.75/2.15  
% 5.75/2.15  
% 5.75/2.15  %Foreground operators:
% 5.75/2.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.75/2.15  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.75/2.15  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.75/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.75/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.15  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.75/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.75/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.75/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.75/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.15  
% 5.75/2.18  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 5.75/2.18  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 5.75/2.18  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.75/2.18  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.75/2.18  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.75/2.18  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.75/2.18  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.75/2.18  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 5.75/2.18  tff(f_62, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.75/2.18  tff(f_54, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 5.75/2.18  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_50, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_55, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 5.75/2.18  tff(c_46, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_57, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 5.75/2.18  tff(c_42, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_56, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 5.75/2.18  tff(c_54, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_54])).
% 5.75/2.18  tff(c_36, plain, (![D_54]: (~r2_hidden('#skF_2', D_54) | ~r1_tarski(D_54, '#skF_3') | ~v3_pre_topc(D_54, '#skF_1') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_357, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 5.75/2.18  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_394, plain, (![B_150, A_151, C_152]: (r1_tarski(B_150, k1_tops_1(A_151, C_152)) | ~r1_tarski(B_150, C_152) | ~v3_pre_topc(B_150, A_151) | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.75/2.18  tff(c_403, plain, (![B_150]: (r1_tarski(B_150, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_150, '#skF_3') | ~v3_pre_topc(B_150, '#skF_1') | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_394])).
% 5.75/2.18  tff(c_412, plain, (![B_153]: (r1_tarski(B_153, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_153, '#skF_3') | ~v3_pre_topc(B_153, '#skF_1') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_403])).
% 5.75/2.18  tff(c_419, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_412])).
% 5.75/2.18  tff(c_432, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_57, c_419])).
% 5.75/2.18  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.75/2.18  tff(c_101, plain, (![A_68, C_69, B_70]: (m1_subset_1(A_68, C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.75/2.18  tff(c_129, plain, (![A_75, B_76, A_77]: (m1_subset_1(A_75, B_76) | ~r2_hidden(A_75, A_77) | ~r1_tarski(A_77, B_76))), inference(resolution, [status(thm)], [c_6, c_101])).
% 5.75/2.18  tff(c_135, plain, (![B_76]: (m1_subset_1('#skF_2', B_76) | ~r1_tarski('#skF_4', B_76))), inference(resolution, [status(thm)], [c_56, c_129])).
% 5.75/2.18  tff(c_449, plain, (m1_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_432, c_135])).
% 5.75/2.18  tff(c_111, plain, (![A_71, B_72]: (r1_tarski(k1_tops_1(A_71, B_72), B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.18  tff(c_118, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_111])).
% 5.75/2.18  tff(c_125, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_118])).
% 5.75/2.18  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.75/2.18  tff(c_181, plain, (![A_86, B_87, B_88]: (m1_subset_1(A_86, B_87) | ~r1_tarski(B_88, B_87) | v1_xboole_0(B_88) | ~m1_subset_1(A_86, B_88))), inference(resolution, [status(thm)], [c_2, c_129])).
% 5.75/2.18  tff(c_196, plain, (![A_86]: (m1_subset_1(A_86, '#skF_3') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(A_86, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_125, c_181])).
% 5.75/2.18  tff(c_228, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_196])).
% 5.75/2.18  tff(c_279, plain, (![B_119, A_120, C_121]: (r1_tarski(B_119, k1_tops_1(A_120, C_121)) | ~r1_tarski(B_119, C_121) | ~v3_pre_topc(B_119, A_120) | ~m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.75/2.18  tff(c_288, plain, (![B_119]: (r1_tarski(B_119, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_119, '#skF_3') | ~v3_pre_topc(B_119, '#skF_1') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_279])).
% 5.75/2.18  tff(c_297, plain, (![B_122]: (r1_tarski(B_122, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_122, '#skF_3') | ~v3_pre_topc(B_122, '#skF_1') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_288])).
% 5.75/2.18  tff(c_304, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_297])).
% 5.75/2.18  tff(c_317, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_57, c_304])).
% 5.75/2.18  tff(c_69, plain, (![C_61, B_62, A_63]: (~v1_xboole_0(C_61) | ~m1_subset_1(B_62, k1_zfmisc_1(C_61)) | ~r2_hidden(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.18  tff(c_77, plain, (![B_64, A_65, A_66]: (~v1_xboole_0(B_64) | ~r2_hidden(A_65, A_66) | ~r1_tarski(A_66, B_64))), inference(resolution, [status(thm)], [c_6, c_69])).
% 5.75/2.18  tff(c_83, plain, (![B_64]: (~v1_xboole_0(B_64) | ~r1_tarski('#skF_4', B_64))), inference(resolution, [status(thm)], [c_56, c_77])).
% 5.75/2.18  tff(c_329, plain, (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_317, c_83])).
% 5.75/2.18  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_329])).
% 5.75/2.18  tff(c_341, plain, (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_196])).
% 5.75/2.18  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_514, plain, (![C_156, A_157, B_158]: (m1_connsp_2(C_156, A_157, B_158) | ~r2_hidden(B_158, k1_tops_1(A_157, C_156)) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(A_157))) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.18  tff(c_931, plain, (![C_194, A_195, A_196]: (m1_connsp_2(C_194, A_195, A_196) | ~m1_subset_1(C_194, k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_subset_1(A_196, u1_struct_0(A_195)) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195) | v1_xboole_0(k1_tops_1(A_195, C_194)) | ~m1_subset_1(A_196, k1_tops_1(A_195, C_194)))), inference(resolution, [status(thm)], [c_2, c_514])).
% 5.75/2.18  tff(c_940, plain, (![A_196]: (m1_connsp_2('#skF_3', '#skF_1', A_196) | ~m1_subset_1(A_196, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(A_196, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_931])).
% 5.75/2.18  tff(c_949, plain, (![A_196]: (m1_connsp_2('#skF_3', '#skF_1', A_196) | ~m1_subset_1(A_196, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(A_196, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_940])).
% 5.75/2.18  tff(c_951, plain, (![A_197]: (m1_connsp_2('#skF_3', '#skF_1', A_197) | ~m1_subset_1(A_197, u1_struct_0('#skF_1')) | ~m1_subset_1(A_197, k1_tops_1('#skF_1', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_341, c_34, c_949])).
% 5.75/2.18  tff(c_954, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_449, c_951])).
% 5.75/2.18  tff(c_957, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_954])).
% 5.75/2.18  tff(c_959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_957])).
% 5.75/2.18  tff(c_962, plain, (![D_198]: (~r2_hidden('#skF_2', D_198) | ~r1_tarski(D_198, '#skF_3') | ~v3_pre_topc(D_198, '#skF_1') | ~m1_subset_1(D_198, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_36])).
% 5.75/2.18  tff(c_969, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_962])).
% 5.75/2.18  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_57, c_56, c_969])).
% 5.75/2.18  tff(c_984, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 5.75/2.18  tff(c_58, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.75/2.18  tff(c_62, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_58])).
% 5.75/2.18  tff(c_1036, plain, (![A_215, B_216]: (r1_tarski(k1_tops_1(A_215, B_216), B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.18  tff(c_1041, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1036])).
% 5.75/2.18  tff(c_1045, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1041])).
% 5.75/2.18  tff(c_1353, plain, (![B_277, A_278, C_279]: (r2_hidden(B_277, k1_tops_1(A_278, C_279)) | ~m1_connsp_2(C_279, A_278, B_277) | ~m1_subset_1(C_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~m1_subset_1(B_277, u1_struct_0(A_278)) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.18  tff(c_1360, plain, (![B_277]: (r2_hidden(B_277, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_277) | ~m1_subset_1(B_277, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1353])).
% 5.75/2.18  tff(c_1365, plain, (![B_277]: (r2_hidden(B_277, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_277) | ~m1_subset_1(B_277, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1360])).
% 5.75/2.18  tff(c_1367, plain, (![B_280]: (r2_hidden(B_280, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_280) | ~m1_subset_1(B_280, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_1365])).
% 5.75/2.18  tff(c_1061, plain, (![A_219, B_220]: (v3_pre_topc(k1_tops_1(A_219, B_220), A_219) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.75/2.18  tff(c_1067, plain, (![A_219, A_3]: (v3_pre_topc(k1_tops_1(A_219, A_3), A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | ~r1_tarski(A_3, u1_struct_0(A_219)))), inference(resolution, [status(thm)], [c_6, c_1061])).
% 5.75/2.18  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(k1_tops_1(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.75/2.18  tff(c_1110, plain, (![D_232]: (~r2_hidden('#skF_2', D_232) | ~r1_tarski(D_232, '#skF_3') | ~v3_pre_topc(D_232, '#skF_1') | ~m1_subset_1(D_232, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_36])).
% 5.75/2.18  tff(c_1114, plain, (![B_12]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_12)) | ~r1_tarski(k1_tops_1('#skF_1', B_12), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_12), '#skF_1') | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_1110])).
% 5.75/2.18  tff(c_1161, plain, (![B_248]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_248)) | ~r1_tarski(k1_tops_1('#skF_1', B_248), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_248), '#skF_1') | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1114])).
% 5.75/2.18  tff(c_1199, plain, (![A_255]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_255)) | ~r1_tarski(k1_tops_1('#skF_1', A_255), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_255), '#skF_1') | ~r1_tarski(A_255, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1161])).
% 5.75/2.18  tff(c_1207, plain, (![A_3]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_3)) | ~r1_tarski(k1_tops_1('#skF_1', A_3), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_3, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1067, c_1199])).
% 5.75/2.18  tff(c_1216, plain, (![A_3]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_3)) | ~r1_tarski(k1_tops_1('#skF_1', A_3), '#skF_3') | ~r1_tarski(A_3, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1207])).
% 5.75/2.18  tff(c_1373, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1367, c_1216])).
% 5.75/2.18  tff(c_1392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_984, c_62, c_1045, c_1373])).
% 5.75/2.18  tff(c_1393, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.75/2.18  tff(c_1397, plain, (![A_283, B_284]: (r1_tarski(A_283, B_284) | ~m1_subset_1(A_283, k1_zfmisc_1(B_284)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.75/2.18  tff(c_1405, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1397])).
% 5.75/2.18  tff(c_1444, plain, (![A_305, B_306]: (r1_tarski(k1_tops_1(A_305, B_306), B_306) | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.18  tff(c_1449, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1444])).
% 5.75/2.18  tff(c_1453, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1449])).
% 5.75/2.18  tff(c_1750, plain, (![B_370, A_371, C_372]: (r2_hidden(B_370, k1_tops_1(A_371, C_372)) | ~m1_connsp_2(C_372, A_371, B_370) | ~m1_subset_1(C_372, k1_zfmisc_1(u1_struct_0(A_371))) | ~m1_subset_1(B_370, u1_struct_0(A_371)) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.18  tff(c_1757, plain, (![B_370]: (r2_hidden(B_370, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_370) | ~m1_subset_1(B_370, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1750])).
% 5.75/2.18  tff(c_1762, plain, (![B_370]: (r2_hidden(B_370, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_370) | ~m1_subset_1(B_370, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1757])).
% 5.75/2.18  tff(c_1764, plain, (![B_373]: (r2_hidden(B_373, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_373) | ~m1_subset_1(B_373, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_1762])).
% 5.75/2.18  tff(c_1498, plain, (![A_317, B_318]: (v3_pre_topc(k1_tops_1(A_317, B_318), A_317) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(A_317))) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.75/2.18  tff(c_1507, plain, (![A_317, A_3]: (v3_pre_topc(k1_tops_1(A_317, A_3), A_317) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317) | ~r1_tarski(A_3, u1_struct_0(A_317)))), inference(resolution, [status(thm)], [c_6, c_1498])).
% 5.75/2.18  tff(c_1394, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 5.75/2.18  tff(c_44, plain, (![D_54]: (~r2_hidden('#skF_2', D_54) | ~r1_tarski(D_54, '#skF_3') | ~v3_pre_topc(D_54, '#skF_1') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_1512, plain, (![D_319]: (~r2_hidden('#skF_2', D_319) | ~r1_tarski(D_319, '#skF_3') | ~v3_pre_topc(D_319, '#skF_1') | ~m1_subset_1(D_319, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1394, c_44])).
% 5.75/2.18  tff(c_1516, plain, (![B_12]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_12)) | ~r1_tarski(k1_tops_1('#skF_1', B_12), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_12), '#skF_1') | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_1512])).
% 5.75/2.18  tff(c_1673, plain, (![B_360]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_360)) | ~r1_tarski(k1_tops_1('#skF_1', B_360), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_360), '#skF_1') | ~m1_subset_1(B_360, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1516])).
% 5.75/2.18  tff(c_1696, plain, (![A_361]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_361)) | ~r1_tarski(k1_tops_1('#skF_1', A_361), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_361), '#skF_1') | ~r1_tarski(A_361, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1673])).
% 5.75/2.18  tff(c_1704, plain, (![A_3]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_3)) | ~r1_tarski(k1_tops_1('#skF_1', A_3), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_3, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1507, c_1696])).
% 5.75/2.18  tff(c_1713, plain, (![A_3]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_3)) | ~r1_tarski(k1_tops_1('#skF_1', A_3), '#skF_3') | ~r1_tarski(A_3, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1704])).
% 5.75/2.18  tff(c_1768, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1764, c_1713])).
% 5.75/2.18  tff(c_1785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1393, c_1405, c_1453, c_1768])).
% 5.75/2.18  tff(c_1786, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 5.75/2.18  tff(c_1790, plain, (![A_376, B_377]: (r1_tarski(A_376, B_377) | ~m1_subset_1(A_376, k1_zfmisc_1(B_377)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.75/2.18  tff(c_1798, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1790])).
% 5.75/2.18  tff(c_1834, plain, (![A_396, B_397]: (r1_tarski(k1_tops_1(A_396, B_397), B_397) | ~m1_subset_1(B_397, k1_zfmisc_1(u1_struct_0(A_396))) | ~l1_pre_topc(A_396))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.18  tff(c_1839, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1834])).
% 5.75/2.18  tff(c_1843, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1839])).
% 5.75/2.18  tff(c_2393, plain, (![B_511, A_512, C_513]: (r2_hidden(B_511, k1_tops_1(A_512, C_513)) | ~m1_connsp_2(C_513, A_512, B_511) | ~m1_subset_1(C_513, k1_zfmisc_1(u1_struct_0(A_512))) | ~m1_subset_1(B_511, u1_struct_0(A_512)) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.18  tff(c_2400, plain, (![B_511]: (r2_hidden(B_511, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_511) | ~m1_subset_1(B_511, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_2393])).
% 5.75/2.18  tff(c_2405, plain, (![B_511]: (r2_hidden(B_511, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_511) | ~m1_subset_1(B_511, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2400])).
% 5.75/2.18  tff(c_2407, plain, (![B_514]: (r2_hidden(B_514, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_514) | ~m1_subset_1(B_514, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_2405])).
% 5.75/2.18  tff(c_2185, plain, (![A_460, B_461]: (v3_pre_topc(k1_tops_1(A_460, B_461), A_460) | ~m1_subset_1(B_461, k1_zfmisc_1(u1_struct_0(A_460))) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.75/2.18  tff(c_2194, plain, (![A_460, A_3]: (v3_pre_topc(k1_tops_1(A_460, A_3), A_460) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | ~r1_tarski(A_3, u1_struct_0(A_460)))), inference(resolution, [status(thm)], [c_6, c_2185])).
% 5.75/2.18  tff(c_2140, plain, (![A_455, B_456]: (m1_subset_1(k1_tops_1(A_455, B_456), k1_zfmisc_1(u1_struct_0(A_455))) | ~m1_subset_1(B_456, k1_zfmisc_1(u1_struct_0(A_455))) | ~l1_pre_topc(A_455))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.75/2.18  tff(c_1787, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 5.75/2.18  tff(c_40, plain, (![D_54]: (~r2_hidden('#skF_2', D_54) | ~r1_tarski(D_54, '#skF_3') | ~v3_pre_topc(D_54, '#skF_1') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_1861, plain, (![D_54]: (~r2_hidden('#skF_2', D_54) | ~r1_tarski(D_54, '#skF_3') | ~v3_pre_topc(D_54, '#skF_1') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1787, c_40])).
% 5.75/2.18  tff(c_2144, plain, (![B_456]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_456)) | ~r1_tarski(k1_tops_1('#skF_1', B_456), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_456), '#skF_1') | ~m1_subset_1(B_456, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_2140, c_1861])).
% 5.75/2.18  tff(c_2315, plain, (![B_501]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_501)) | ~r1_tarski(k1_tops_1('#skF_1', B_501), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_501), '#skF_1') | ~m1_subset_1(B_501, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2144])).
% 5.75/2.18  tff(c_2339, plain, (![A_502]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_502)) | ~r1_tarski(k1_tops_1('#skF_1', A_502), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_502), '#skF_1') | ~r1_tarski(A_502, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_2315])).
% 5.75/2.18  tff(c_2347, plain, (![A_3]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_3)) | ~r1_tarski(k1_tops_1('#skF_1', A_3), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_3, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2194, c_2339])).
% 5.75/2.18  tff(c_2356, plain, (![A_3]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_3)) | ~r1_tarski(k1_tops_1('#skF_1', A_3), '#skF_3') | ~r1_tarski(A_3, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2347])).
% 5.75/2.18  tff(c_2411, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2407, c_2356])).
% 5.75/2.18  tff(c_2428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1786, c_1798, c_1843, c_2411])).
% 5.75/2.18  tff(c_2429, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 5.75/2.18  tff(c_2434, plain, (![A_517, B_518]: (r1_tarski(A_517, B_518) | ~m1_subset_1(A_517, k1_zfmisc_1(B_518)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.75/2.18  tff(c_2442, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_2434])).
% 5.75/2.18  tff(c_2477, plain, (![A_540, B_541]: (r1_tarski(k1_tops_1(A_540, B_541), B_541) | ~m1_subset_1(B_541, k1_zfmisc_1(u1_struct_0(A_540))) | ~l1_pre_topc(A_540))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.75/2.18  tff(c_2482, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2477])).
% 5.75/2.18  tff(c_2486, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2482])).
% 5.75/2.18  tff(c_3367, plain, (![B_709, A_710, C_711]: (r2_hidden(B_709, k1_tops_1(A_710, C_711)) | ~m1_connsp_2(C_711, A_710, B_709) | ~m1_subset_1(C_711, k1_zfmisc_1(u1_struct_0(A_710))) | ~m1_subset_1(B_709, u1_struct_0(A_710)) | ~l1_pre_topc(A_710) | ~v2_pre_topc(A_710) | v2_struct_0(A_710))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.18  tff(c_3374, plain, (![B_709]: (r2_hidden(B_709, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_709) | ~m1_subset_1(B_709, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_3367])).
% 5.75/2.18  tff(c_3379, plain, (![B_709]: (r2_hidden(B_709, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_709) | ~m1_subset_1(B_709, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3374])).
% 5.75/2.18  tff(c_3381, plain, (![B_712]: (r2_hidden(B_712, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_712) | ~m1_subset_1(B_712, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_3379])).
% 5.75/2.18  tff(c_2785, plain, (![A_598, B_599]: (v3_pre_topc(k1_tops_1(A_598, B_599), A_598) | ~m1_subset_1(B_599, k1_zfmisc_1(u1_struct_0(A_598))) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.75/2.18  tff(c_2791, plain, (![A_598, A_3]: (v3_pre_topc(k1_tops_1(A_598, A_3), A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | ~r1_tarski(A_3, u1_struct_0(A_598)))), inference(resolution, [status(thm)], [c_6, c_2785])).
% 5.75/2.18  tff(c_3144, plain, (![A_669, B_670]: (m1_subset_1(k1_tops_1(A_669, B_670), k1_zfmisc_1(u1_struct_0(A_669))) | ~m1_subset_1(B_670, k1_zfmisc_1(u1_struct_0(A_669))) | ~l1_pre_topc(A_669))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.75/2.18  tff(c_2430, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 5.75/2.18  tff(c_48, plain, (![D_54]: (~r2_hidden('#skF_2', D_54) | ~r1_tarski(D_54, '#skF_3') | ~v3_pre_topc(D_54, '#skF_1') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.75/2.18  tff(c_3120, plain, (![D_54]: (~r2_hidden('#skF_2', D_54) | ~r1_tarski(D_54, '#skF_3') | ~v3_pre_topc(D_54, '#skF_1') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2430, c_48])).
% 5.75/2.18  tff(c_3148, plain, (![B_670]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_670)) | ~r1_tarski(k1_tops_1('#skF_1', B_670), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_670), '#skF_1') | ~m1_subset_1(B_670, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_3144, c_3120])).
% 5.75/2.18  tff(c_3225, plain, (![B_698]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_698)) | ~r1_tarski(k1_tops_1('#skF_1', B_698), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_698), '#skF_1') | ~m1_subset_1(B_698, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3148])).
% 5.75/2.18  tff(c_3249, plain, (![A_699]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_699)) | ~r1_tarski(k1_tops_1('#skF_1', A_699), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_699), '#skF_1') | ~r1_tarski(A_699, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_3225])).
% 5.75/2.18  tff(c_3257, plain, (![A_3]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_3)) | ~r1_tarski(k1_tops_1('#skF_1', A_3), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_3, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2791, c_3249])).
% 5.75/2.18  tff(c_3266, plain, (![A_3]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_3)) | ~r1_tarski(k1_tops_1('#skF_1', A_3), '#skF_3') | ~r1_tarski(A_3, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3257])).
% 5.75/2.18  tff(c_3385, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3381, c_3266])).
% 5.75/2.18  tff(c_3400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2429, c_2442, c_2486, c_3385])).
% 5.75/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.18  
% 5.75/2.18  Inference rules
% 5.75/2.18  ----------------------
% 5.75/2.18  #Ref     : 0
% 5.75/2.18  #Sup     : 674
% 5.75/2.18  #Fact    : 0
% 5.75/2.18  #Define  : 0
% 5.75/2.18  #Split   : 57
% 5.75/2.18  #Chain   : 0
% 5.75/2.18  #Close   : 0
% 5.75/2.18  
% 5.75/2.18  Ordering : KBO
% 5.75/2.18  
% 5.75/2.18  Simplification rules
% 5.75/2.18  ----------------------
% 5.75/2.18  #Subsume      : 162
% 5.75/2.18  #Demod        : 396
% 5.75/2.18  #Tautology    : 72
% 5.75/2.18  #SimpNegUnit  : 76
% 5.75/2.18  #BackRed      : 0
% 5.75/2.18  
% 5.75/2.18  #Partial instantiations: 0
% 5.75/2.18  #Strategies tried      : 1
% 5.75/2.18  
% 5.75/2.18  Timing (in seconds)
% 5.75/2.18  ----------------------
% 5.75/2.18  Preprocessing        : 0.34
% 5.75/2.18  Parsing              : 0.19
% 5.75/2.18  CNF conversion       : 0.02
% 5.75/2.18  Main loop            : 0.96
% 5.75/2.18  Inferencing          : 0.37
% 5.75/2.18  Reduction            : 0.26
% 5.75/2.18  Demodulation         : 0.17
% 5.75/2.18  BG Simplification    : 0.03
% 5.75/2.18  Subsumption          : 0.21
% 5.75/2.18  Abstraction          : 0.04
% 5.75/2.18  MUC search           : 0.00
% 5.75/2.18  Cooper               : 0.00
% 5.75/2.18  Total                : 1.36
% 5.75/2.18  Index Insertion      : 0.00
% 5.75/2.18  Index Deletion       : 0.00
% 5.75/2.18  Index Matching       : 0.00
% 5.75/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
