%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:12 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 429 expanded)
%              Number of leaves         :   26 ( 160 expanded)
%              Depth                    :   13
%              Number of atoms          :  441 (1761 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_71,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_88,axiom,(
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

tff(c_22,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_49,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_51,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_221,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_174,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k1_tops_1(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_192,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k1_tops_1(A_73,B_74),u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_159,plain,(
    ! [A_71,B_72] :
      ( v3_pre_topc(k1_tops_1(A_71,B_72),A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_166,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_173,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_166])).

tff(c_112,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tops_1(A_60,B_61),B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_119,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_112])).

tff(c_126,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_119])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_248,plain,(
    ! [B_95,A_96,C_97] :
      ( r1_tarski(B_95,k1_tops_1(A_96,C_97))
      | ~ r1_tarski(B_95,C_97)
      | ~ v3_pre_topc(B_95,A_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_257,plain,(
    ! [B_95] :
      ( r1_tarski(B_95,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_95,'#skF_3')
      | ~ v3_pre_topc(B_95,'#skF_1')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_248])).

tff(c_266,plain,(
    ! [B_98] :
      ( r1_tarski(B_98,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_98,'#skF_3')
      | ~ v3_pre_topc(B_98,'#skF_1')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_257])).

tff(c_360,plain,(
    ! [A_106] :
      ( r1_tarski(A_106,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_106,'#skF_3')
      | ~ v3_pre_topc(A_106,'#skF_1')
      | ~ r1_tarski(A_106,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_266])).

tff(c_273,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_266])).

tff(c_286,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_51,c_273])).

tff(c_67,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(C_51,A_52)
      | ~ r2_hidden(C_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_2',A_54)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_50,c_67])).

tff(c_85,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_2',B_55)
      | ~ r1_tarski('#skF_4',B_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_2',A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58))
      | ~ r1_tarski('#skF_4',B_59) ) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_108,plain,(
    ! [B_6,A_5] :
      ( r2_hidden('#skF_2',B_6)
      | ~ r1_tarski('#skF_4',A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_296,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_2',B_6)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_6) ) ),
    inference(resolution,[status(thm)],[c_286,c_108])).

tff(c_364,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_360,c_296])).

tff(c_383,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_126,c_364])).

tff(c_418,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_421,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_192,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_421])).

tff(c_426,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_16,plain,(
    ! [C_27,A_21,B_25] :
      ( m1_connsp_2(C_27,A_21,B_25)
      | ~ r2_hidden(B_25,k1_tops_1(A_21,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_25,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_429,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_426,c_16])).

tff(c_434,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_429])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_221,c_434])).

tff(c_440,plain,(
    ! [D_110] :
      ( ~ r2_hidden('#skF_2',D_110)
      | ~ r1_tarski(D_110,'#skF_3')
      | ~ v3_pre_topc(D_110,'#skF_1')
      | ~ m1_subset_1(D_110,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_447,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_440])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_51,c_50,c_447])).

tff(c_462,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_52])).

tff(c_512,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(k1_tops_1(A_123,B_124),B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_517,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_512])).

tff(c_521,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_517])).

tff(c_820,plain,(
    ! [B_170,A_171,C_172] :
      ( r2_hidden(B_170,k1_tops_1(A_171,C_172))
      | ~ m1_connsp_2(C_172,A_171,B_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ m1_subset_1(B_170,u1_struct_0(A_171))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_827,plain,(
    ! [B_170] :
      ( r2_hidden(B_170,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_170)
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_820])).

tff(c_832,plain,(
    ! [B_170] :
      ( r2_hidden(B_170,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_170)
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_827])).

tff(c_834,plain,(
    ! [B_173] :
      ( r2_hidden(B_173,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_173)
      | ~ m1_subset_1(B_173,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_832])).

tff(c_538,plain,(
    ! [A_131,B_132] :
      ( v3_pre_topc(k1_tops_1(A_131,B_132),A_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_544,plain,(
    ! [A_131,A_5] :
      ( v3_pre_topc(k1_tops_1(A_131,A_5),A_131)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | ~ r1_tarski(A_5,u1_struct_0(A_131)) ) ),
    inference(resolution,[status(thm)],[c_6,c_538])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k1_tops_1(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_574,plain,(
    ! [D_143] :
      ( ~ r2_hidden('#skF_2',D_143)
      | ~ r1_tarski(D_143,'#skF_3')
      | ~ v3_pre_topc(D_143,'#skF_1')
      | ~ m1_subset_1(D_143,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_30])).

tff(c_578,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_574])).

tff(c_645,plain,(
    ! [B_155] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_155))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_155),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_155),'#skF_1')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_578])).

tff(c_673,plain,(
    ! [A_158] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_158))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_158),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_158),'#skF_1')
      | ~ r1_tarski(A_158,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_645])).

tff(c_681,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_544,c_673])).

tff(c_690,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_681])).

tff(c_838,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_834,c_690])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_462,c_56,c_521,c_838])).

tff(c_848,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_851,plain,(
    ! [A_174,B_175] :
      ( r1_tarski(A_174,B_175)
      | ~ m1_subset_1(A_174,k1_zfmisc_1(B_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_855,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_851])).

tff(c_871,plain,(
    ! [A_182,B_183] :
      ( r1_tarski(k1_tops_1(A_182,B_183),B_183)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_876,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_871])).

tff(c_880,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_876])).

tff(c_1136,plain,(
    ! [B_231,A_232,C_233] :
      ( r2_hidden(B_231,k1_tops_1(A_232,C_233))
      | ~ m1_connsp_2(C_233,A_232,B_231)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ m1_subset_1(B_231,u1_struct_0(A_232))
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1143,plain,(
    ! [B_231] :
      ( r2_hidden(B_231,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_231)
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_1136])).

tff(c_1148,plain,(
    ! [B_231] :
      ( r2_hidden(B_231,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_231)
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1143])).

tff(c_1150,plain,(
    ! [B_234] :
      ( r2_hidden(B_234,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_234)
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1148])).

tff(c_897,plain,(
    ! [A_191,B_192] :
      ( v3_pre_topc(k1_tops_1(A_191,B_192),A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_903,plain,(
    ! [A_191,A_5] :
      ( v3_pre_topc(k1_tops_1(A_191,A_5),A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | ~ r1_tarski(A_5,u1_struct_0(A_191)) ) ),
    inference(resolution,[status(thm)],[c_6,c_897])).

tff(c_849,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_946,plain,(
    ! [D_207] :
      ( ~ r2_hidden('#skF_2',D_207)
      | ~ r1_tarski(D_207,'#skF_3')
      | ~ v3_pre_topc(D_207,'#skF_1')
      | ~ m1_subset_1(D_207,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_849,c_38])).

tff(c_950,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_946])).

tff(c_984,plain,(
    ! [B_211] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_211))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_211),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_211),'#skF_1')
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_950])).

tff(c_1007,plain,(
    ! [A_212] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_212))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_212),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_212),'#skF_1')
      | ~ r1_tarski(A_212,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_984])).

tff(c_1015,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_903,c_1007])).

tff(c_1024,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1015])).

tff(c_1156,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1150,c_1024])).

tff(c_1169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_848,c_855,c_880,c_1156])).

tff(c_1170,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1173,plain,(
    ! [A_235,B_236] :
      ( r1_tarski(A_235,B_236)
      | ~ m1_subset_1(A_235,k1_zfmisc_1(B_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1177,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_1173])).

tff(c_1185,plain,(
    ! [A_242,B_243] :
      ( r1_tarski(k1_tops_1(A_242,B_243),B_243)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1190,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1185])).

tff(c_1194,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1190])).

tff(c_1535,plain,(
    ! [B_304,A_305,C_306] :
      ( r2_hidden(B_304,k1_tops_1(A_305,C_306))
      | ~ m1_connsp_2(C_306,A_305,B_304)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ m1_subset_1(B_304,u1_struct_0(A_305))
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1542,plain,(
    ! [B_304] :
      ( r2_hidden(B_304,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_304)
      | ~ m1_subset_1(B_304,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_1535])).

tff(c_1547,plain,(
    ! [B_304] :
      ( r2_hidden(B_304,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_304)
      | ~ m1_subset_1(B_304,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1542])).

tff(c_1549,plain,(
    ! [B_307] :
      ( r2_hidden(B_307,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_307)
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1547])).

tff(c_1408,plain,(
    ! [A_277,B_278] :
      ( v3_pre_topc(k1_tops_1(A_277,B_278),A_277)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1417,plain,(
    ! [A_277,A_5] :
      ( v3_pre_topc(k1_tops_1(A_277,A_5),A_277)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | ~ r1_tarski(A_5,u1_struct_0(A_277)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1408])).

tff(c_1171,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1373,plain,(
    ! [D_275] :
      ( ~ r2_hidden('#skF_2',D_275)
      | ~ r1_tarski(D_275,'#skF_3')
      | ~ v3_pre_topc(D_275,'#skF_1')
      | ~ m1_subset_1(D_275,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1171,c_34])).

tff(c_1377,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_1373])).

tff(c_1427,plain,(
    ! [B_285] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_285))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_285),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_285),'#skF_1')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1377])).

tff(c_1446,plain,(
    ! [A_286] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_286))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_286),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_286),'#skF_1')
      | ~ r1_tarski(A_286,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1427])).

tff(c_1454,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1417,c_1446])).

tff(c_1463,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1454])).

tff(c_1555,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1549,c_1463])).

tff(c_1568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1170,c_1177,c_1194,c_1555])).

tff(c_1569,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2233,plain,(
    ! [B_421,A_422,C_423] :
      ( r2_hidden(B_421,k1_tops_1(A_422,C_423))
      | ~ m1_connsp_2(C_423,A_422,B_421)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(u1_struct_0(A_422)))
      | ~ m1_subset_1(B_421,u1_struct_0(A_422))
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2240,plain,(
    ! [B_421] :
      ( r2_hidden(B_421,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_421)
      | ~ m1_subset_1(B_421,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_2233])).

tff(c_2245,plain,(
    ! [B_421] :
      ( r2_hidden(B_421,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_421)
      | ~ m1_subset_1(B_421,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_2240])).

tff(c_2247,plain,(
    ! [B_424] :
      ( r2_hidden(B_424,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_424)
      | ~ m1_subset_1(B_424,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2245])).

tff(c_2019,plain,(
    ! [A_386,B_387] :
      ( v3_pre_topc(k1_tops_1(A_386,B_387),A_386)
      | ~ m1_subset_1(B_387,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2026,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_2019])).

tff(c_2031,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_2026])).

tff(c_1585,plain,(
    ! [A_315,B_316] :
      ( r1_tarski(k1_tops_1(A_315,B_316),B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1590,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1585])).

tff(c_1594,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1590])).

tff(c_1570,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1979,plain,(
    ! [D_382] :
      ( ~ r2_hidden('#skF_2',D_382)
      | ~ r1_tarski(D_382,'#skF_3')
      | ~ v3_pre_topc(D_382,'#skF_1')
      | ~ m1_subset_1(D_382,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1570,c_42])).

tff(c_1983,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_1979])).

tff(c_2087,plain,(
    ! [B_404] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_404))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_404),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_404),'#skF_1')
      | ~ m1_subset_1(B_404,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1983])).

tff(c_2098,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_2087])).

tff(c_2105,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_1594,c_2098])).

tff(c_2250,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2247,c_2105])).

tff(c_2256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1569,c_2250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.83  
% 4.48/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.84  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.48/1.84  
% 4.48/1.84  %Foreground sorts:
% 4.48/1.84  
% 4.48/1.84  
% 4.48/1.84  %Background operators:
% 4.48/1.84  
% 4.48/1.84  
% 4.48/1.84  %Foreground operators:
% 4.48/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.48/1.84  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.48/1.84  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.48/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.48/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.48/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.48/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.48/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.48/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.48/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.48/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.84  
% 4.48/1.87  tff(f_113, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.48/1.87  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.48/1.87  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.48/1.87  tff(f_50, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.48/1.87  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.48/1.87  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 4.48/1.87  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.48/1.87  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.48/1.87  tff(c_22, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_44, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_49, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.48/1.87  tff(c_40, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_51, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 4.48/1.87  tff(c_36, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_50, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 4.48/1.87  tff(c_48, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_48])).
% 4.48/1.87  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_30, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_221, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 4.48/1.87  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_174, plain, (![A_73, B_74]: (m1_subset_1(k1_tops_1(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.48/1.87  tff(c_4, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.48/1.87  tff(c_192, plain, (![A_73, B_74]: (r1_tarski(k1_tops_1(A_73, B_74), u1_struct_0(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_174, c_4])).
% 4.48/1.87  tff(c_159, plain, (![A_71, B_72]: (v3_pre_topc(k1_tops_1(A_71, B_72), A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.87  tff(c_166, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_159])).
% 4.48/1.87  tff(c_173, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_166])).
% 4.48/1.87  tff(c_112, plain, (![A_60, B_61]: (r1_tarski(k1_tops_1(A_60, B_61), B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.48/1.87  tff(c_119, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_112])).
% 4.48/1.87  tff(c_126, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_119])).
% 4.48/1.87  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.48/1.87  tff(c_248, plain, (![B_95, A_96, C_97]: (r1_tarski(B_95, k1_tops_1(A_96, C_97)) | ~r1_tarski(B_95, C_97) | ~v3_pre_topc(B_95, A_96) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.87  tff(c_257, plain, (![B_95]: (r1_tarski(B_95, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_95, '#skF_3') | ~v3_pre_topc(B_95, '#skF_1') | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_248])).
% 4.48/1.87  tff(c_266, plain, (![B_98]: (r1_tarski(B_98, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_98, '#skF_3') | ~v3_pre_topc(B_98, '#skF_1') | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_257])).
% 4.48/1.87  tff(c_360, plain, (![A_106]: (r1_tarski(A_106, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_106, '#skF_3') | ~v3_pre_topc(A_106, '#skF_1') | ~r1_tarski(A_106, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_266])).
% 4.48/1.87  tff(c_273, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_266])).
% 4.48/1.87  tff(c_286, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_51, c_273])).
% 4.48/1.87  tff(c_67, plain, (![C_51, A_52, B_53]: (r2_hidden(C_51, A_52) | ~r2_hidden(C_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.48/1.87  tff(c_71, plain, (![A_54]: (r2_hidden('#skF_2', A_54) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_54)))), inference(resolution, [status(thm)], [c_50, c_67])).
% 4.48/1.87  tff(c_85, plain, (![B_55]: (r2_hidden('#skF_2', B_55) | ~r1_tarski('#skF_4', B_55))), inference(resolution, [status(thm)], [c_6, c_71])).
% 4.48/1.87  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.48/1.87  tff(c_96, plain, (![A_58, B_59]: (r2_hidden('#skF_2', A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)) | ~r1_tarski('#skF_4', B_59))), inference(resolution, [status(thm)], [c_85, c_2])).
% 4.48/1.87  tff(c_108, plain, (![B_6, A_5]: (r2_hidden('#skF_2', B_6) | ~r1_tarski('#skF_4', A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_6, c_96])).
% 4.48/1.87  tff(c_296, plain, (![B_6]: (r2_hidden('#skF_2', B_6) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_6))), inference(resolution, [status(thm)], [c_286, c_108])).
% 4.48/1.87  tff(c_364, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_360, c_296])).
% 4.48/1.87  tff(c_383, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_126, c_364])).
% 4.48/1.87  tff(c_418, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_383])).
% 4.48/1.87  tff(c_421, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_192, c_418])).
% 4.48/1.87  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_421])).
% 4.48/1.87  tff(c_426, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_383])).
% 4.48/1.87  tff(c_16, plain, (![C_27, A_21, B_25]: (m1_connsp_2(C_27, A_21, B_25) | ~r2_hidden(B_25, k1_tops_1(A_21, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_25, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.48/1.87  tff(c_429, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_426, c_16])).
% 4.48/1.87  tff(c_434, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_429])).
% 4.48/1.87  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_221, c_434])).
% 4.48/1.87  tff(c_440, plain, (![D_110]: (~r2_hidden('#skF_2', D_110) | ~r1_tarski(D_110, '#skF_3') | ~v3_pre_topc(D_110, '#skF_1') | ~m1_subset_1(D_110, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_30])).
% 4.48/1.87  tff(c_447, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_440])).
% 4.48/1.87  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_51, c_50, c_447])).
% 4.48/1.87  tff(c_462, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.48/1.87  tff(c_52, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.48/1.87  tff(c_56, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_52])).
% 4.48/1.87  tff(c_512, plain, (![A_123, B_124]: (r1_tarski(k1_tops_1(A_123, B_124), B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.48/1.87  tff(c_517, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_512])).
% 4.48/1.87  tff(c_521, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_517])).
% 4.48/1.87  tff(c_820, plain, (![B_170, A_171, C_172]: (r2_hidden(B_170, k1_tops_1(A_171, C_172)) | ~m1_connsp_2(C_172, A_171, B_170) | ~m1_subset_1(C_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~m1_subset_1(B_170, u1_struct_0(A_171)) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.48/1.87  tff(c_827, plain, (![B_170]: (r2_hidden(B_170, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_170) | ~m1_subset_1(B_170, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_820])).
% 4.48/1.87  tff(c_832, plain, (![B_170]: (r2_hidden(B_170, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_170) | ~m1_subset_1(B_170, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_827])).
% 4.48/1.87  tff(c_834, plain, (![B_173]: (r2_hidden(B_173, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_173) | ~m1_subset_1(B_173, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_28, c_832])).
% 4.48/1.87  tff(c_538, plain, (![A_131, B_132]: (v3_pre_topc(k1_tops_1(A_131, B_132), A_131) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.87  tff(c_544, plain, (![A_131, A_5]: (v3_pre_topc(k1_tops_1(A_131, A_5), A_131) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | ~r1_tarski(A_5, u1_struct_0(A_131)))), inference(resolution, [status(thm)], [c_6, c_538])).
% 4.48/1.87  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(k1_tops_1(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.48/1.87  tff(c_574, plain, (![D_143]: (~r2_hidden('#skF_2', D_143) | ~r1_tarski(D_143, '#skF_3') | ~v3_pre_topc(D_143, '#skF_1') | ~m1_subset_1(D_143, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_30])).
% 4.48/1.87  tff(c_578, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_574])).
% 4.48/1.87  tff(c_645, plain, (![B_155]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_155)) | ~r1_tarski(k1_tops_1('#skF_1', B_155), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_155), '#skF_1') | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_578])).
% 4.48/1.87  tff(c_673, plain, (![A_158]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_158)) | ~r1_tarski(k1_tops_1('#skF_1', A_158), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_158), '#skF_1') | ~r1_tarski(A_158, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_645])).
% 4.48/1.87  tff(c_681, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_544, c_673])).
% 4.48/1.87  tff(c_690, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_681])).
% 4.48/1.87  tff(c_838, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_834, c_690])).
% 4.48/1.87  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_462, c_56, c_521, c_838])).
% 4.48/1.87  tff(c_848, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.48/1.87  tff(c_851, plain, (![A_174, B_175]: (r1_tarski(A_174, B_175) | ~m1_subset_1(A_174, k1_zfmisc_1(B_175)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.48/1.87  tff(c_855, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_851])).
% 4.48/1.87  tff(c_871, plain, (![A_182, B_183]: (r1_tarski(k1_tops_1(A_182, B_183), B_183) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.48/1.87  tff(c_876, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_871])).
% 4.48/1.87  tff(c_880, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_876])).
% 4.48/1.87  tff(c_1136, plain, (![B_231, A_232, C_233]: (r2_hidden(B_231, k1_tops_1(A_232, C_233)) | ~m1_connsp_2(C_233, A_232, B_231) | ~m1_subset_1(C_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~m1_subset_1(B_231, u1_struct_0(A_232)) | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.48/1.87  tff(c_1143, plain, (![B_231]: (r2_hidden(B_231, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_231) | ~m1_subset_1(B_231, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_1136])).
% 4.48/1.87  tff(c_1148, plain, (![B_231]: (r2_hidden(B_231, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_231) | ~m1_subset_1(B_231, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1143])).
% 4.48/1.87  tff(c_1150, plain, (![B_234]: (r2_hidden(B_234, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_234) | ~m1_subset_1(B_234, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_28, c_1148])).
% 4.48/1.87  tff(c_897, plain, (![A_191, B_192]: (v3_pre_topc(k1_tops_1(A_191, B_192), A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.87  tff(c_903, plain, (![A_191, A_5]: (v3_pre_topc(k1_tops_1(A_191, A_5), A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | ~r1_tarski(A_5, u1_struct_0(A_191)))), inference(resolution, [status(thm)], [c_6, c_897])).
% 4.48/1.87  tff(c_849, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 4.48/1.87  tff(c_38, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_946, plain, (![D_207]: (~r2_hidden('#skF_2', D_207) | ~r1_tarski(D_207, '#skF_3') | ~v3_pre_topc(D_207, '#skF_1') | ~m1_subset_1(D_207, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_849, c_38])).
% 4.48/1.87  tff(c_950, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_946])).
% 4.48/1.87  tff(c_984, plain, (![B_211]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_211)) | ~r1_tarski(k1_tops_1('#skF_1', B_211), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_211), '#skF_1') | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_950])).
% 4.48/1.87  tff(c_1007, plain, (![A_212]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_212)) | ~r1_tarski(k1_tops_1('#skF_1', A_212), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_212), '#skF_1') | ~r1_tarski(A_212, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_984])).
% 4.48/1.87  tff(c_1015, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_903, c_1007])).
% 4.48/1.87  tff(c_1024, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1015])).
% 4.48/1.87  tff(c_1156, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1150, c_1024])).
% 4.48/1.87  tff(c_1169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_848, c_855, c_880, c_1156])).
% 4.48/1.87  tff(c_1170, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 4.48/1.87  tff(c_1173, plain, (![A_235, B_236]: (r1_tarski(A_235, B_236) | ~m1_subset_1(A_235, k1_zfmisc_1(B_236)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.48/1.87  tff(c_1177, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_1173])).
% 4.48/1.87  tff(c_1185, plain, (![A_242, B_243]: (r1_tarski(k1_tops_1(A_242, B_243), B_243) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.48/1.87  tff(c_1190, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1185])).
% 4.48/1.87  tff(c_1194, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1190])).
% 4.48/1.87  tff(c_1535, plain, (![B_304, A_305, C_306]: (r2_hidden(B_304, k1_tops_1(A_305, C_306)) | ~m1_connsp_2(C_306, A_305, B_304) | ~m1_subset_1(C_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~m1_subset_1(B_304, u1_struct_0(A_305)) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.48/1.87  tff(c_1542, plain, (![B_304]: (r2_hidden(B_304, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_304) | ~m1_subset_1(B_304, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_1535])).
% 4.48/1.87  tff(c_1547, plain, (![B_304]: (r2_hidden(B_304, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_304) | ~m1_subset_1(B_304, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1542])).
% 4.48/1.87  tff(c_1549, plain, (![B_307]: (r2_hidden(B_307, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_307) | ~m1_subset_1(B_307, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_28, c_1547])).
% 4.48/1.87  tff(c_1408, plain, (![A_277, B_278]: (v3_pre_topc(k1_tops_1(A_277, B_278), A_277) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_277))) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.87  tff(c_1417, plain, (![A_277, A_5]: (v3_pre_topc(k1_tops_1(A_277, A_5), A_277) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | ~r1_tarski(A_5, u1_struct_0(A_277)))), inference(resolution, [status(thm)], [c_6, c_1408])).
% 4.48/1.87  tff(c_1171, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 4.48/1.87  tff(c_34, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_1373, plain, (![D_275]: (~r2_hidden('#skF_2', D_275) | ~r1_tarski(D_275, '#skF_3') | ~v3_pre_topc(D_275, '#skF_1') | ~m1_subset_1(D_275, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1171, c_34])).
% 4.48/1.87  tff(c_1377, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1373])).
% 4.48/1.87  tff(c_1427, plain, (![B_285]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_285)) | ~r1_tarski(k1_tops_1('#skF_1', B_285), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_285), '#skF_1') | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1377])).
% 4.48/1.87  tff(c_1446, plain, (![A_286]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_286)) | ~r1_tarski(k1_tops_1('#skF_1', A_286), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_286), '#skF_1') | ~r1_tarski(A_286, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1427])).
% 4.48/1.87  tff(c_1454, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1417, c_1446])).
% 4.48/1.87  tff(c_1463, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1454])).
% 4.48/1.87  tff(c_1555, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1549, c_1463])).
% 4.48/1.87  tff(c_1568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1170, c_1177, c_1194, c_1555])).
% 4.48/1.87  tff(c_1569, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.48/1.87  tff(c_2233, plain, (![B_421, A_422, C_423]: (r2_hidden(B_421, k1_tops_1(A_422, C_423)) | ~m1_connsp_2(C_423, A_422, B_421) | ~m1_subset_1(C_423, k1_zfmisc_1(u1_struct_0(A_422))) | ~m1_subset_1(B_421, u1_struct_0(A_422)) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.48/1.87  tff(c_2240, plain, (![B_421]: (r2_hidden(B_421, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_421) | ~m1_subset_1(B_421, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_2233])).
% 4.48/1.87  tff(c_2245, plain, (![B_421]: (r2_hidden(B_421, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_421) | ~m1_subset_1(B_421, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_2240])).
% 4.48/1.87  tff(c_2247, plain, (![B_424]: (r2_hidden(B_424, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_424) | ~m1_subset_1(B_424, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_28, c_2245])).
% 4.48/1.87  tff(c_2019, plain, (![A_386, B_387]: (v3_pre_topc(k1_tops_1(A_386, B_387), A_386) | ~m1_subset_1(B_387, k1_zfmisc_1(u1_struct_0(A_386))) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.87  tff(c_2026, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_2019])).
% 4.48/1.87  tff(c_2031, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_2026])).
% 4.48/1.87  tff(c_1585, plain, (![A_315, B_316]: (r1_tarski(k1_tops_1(A_315, B_316), B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.48/1.87  tff(c_1590, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1585])).
% 4.48/1.87  tff(c_1594, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1590])).
% 4.48/1.87  tff(c_1570, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.48/1.87  tff(c_42, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.48/1.87  tff(c_1979, plain, (![D_382]: (~r2_hidden('#skF_2', D_382) | ~r1_tarski(D_382, '#skF_3') | ~v3_pre_topc(D_382, '#skF_1') | ~m1_subset_1(D_382, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1570, c_42])).
% 4.48/1.87  tff(c_1983, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1979])).
% 4.48/1.87  tff(c_2087, plain, (![B_404]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_404)) | ~r1_tarski(k1_tops_1('#skF_1', B_404), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_404), '#skF_1') | ~m1_subset_1(B_404, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1983])).
% 4.48/1.87  tff(c_2098, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_20, c_2087])).
% 4.48/1.87  tff(c_2105, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_1594, c_2098])).
% 4.48/1.87  tff(c_2250, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2247, c_2105])).
% 4.48/1.87  tff(c_2256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1569, c_2250])).
% 4.48/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.87  
% 4.48/1.87  Inference rules
% 4.48/1.87  ----------------------
% 4.48/1.87  #Ref     : 0
% 4.48/1.87  #Sup     : 396
% 4.48/1.87  #Fact    : 0
% 4.48/1.87  #Define  : 0
% 4.48/1.87  #Split   : 22
% 4.48/1.87  #Chain   : 0
% 4.48/1.87  #Close   : 0
% 4.48/1.87  
% 4.48/1.87  Ordering : KBO
% 4.48/1.87  
% 4.48/1.87  Simplification rules
% 4.48/1.87  ----------------------
% 4.48/1.87  #Subsume      : 95
% 4.48/1.87  #Demod        : 317
% 4.48/1.87  #Tautology    : 43
% 4.48/1.87  #SimpNegUnit  : 26
% 4.48/1.87  #BackRed      : 0
% 4.48/1.87  
% 4.48/1.87  #Partial instantiations: 0
% 4.48/1.87  #Strategies tried      : 1
% 4.48/1.87  
% 4.48/1.87  Timing (in seconds)
% 4.48/1.87  ----------------------
% 4.48/1.87  Preprocessing        : 0.32
% 4.48/1.87  Parsing              : 0.18
% 4.48/1.87  CNF conversion       : 0.02
% 4.48/1.87  Main loop            : 0.72
% 4.48/1.87  Inferencing          : 0.28
% 4.48/1.87  Reduction            : 0.19
% 4.48/1.87  Demodulation         : 0.13
% 4.48/1.87  BG Simplification    : 0.03
% 4.48/1.87  Subsumption          : 0.16
% 4.48/1.87  Abstraction          : 0.03
% 4.48/1.87  MUC search           : 0.00
% 4.48/1.87  Cooper               : 0.00
% 4.48/1.87  Total                : 1.11
% 4.48/1.87  Index Insertion      : 0.00
% 4.48/1.87  Index Deletion       : 0.00
% 4.48/1.87  Index Matching       : 0.00
% 4.48/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
