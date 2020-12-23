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
% DateTime   : Thu Dec  3 10:24:13 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 410 expanded)
%              Number of leaves         :   26 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  379 (1593 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_127,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_63,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_53,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_64,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_908,plain,(
    ! [A_133] :
      ( r1_tarski(A_133,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_133,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_61,c_64])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_51,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_50,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_71,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    ! [D_51] :
      ( ~ r2_hidden('#skF_2',D_51)
      | ~ r1_tarski(D_51,'#skF_3')
      | ~ v3_pre_topc(D_51,'#skF_1')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_289,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_219,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_tops_1(A_77,B_78),B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_226,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_219])).

tff(c_233,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_226])).

tff(c_70,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_56,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_61,c_64])).

tff(c_273,plain,(
    ! [A_82,B_83] :
      ( v3_pre_topc(k1_tops_1(A_82,B_83),A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_280,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_273])).

tff(c_287,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_280])).

tff(c_421,plain,(
    ! [B_104,A_105,C_106] :
      ( r1_tarski(B_104,k1_tops_1(A_105,C_106))
      | ~ r1_tarski(B_104,C_106)
      | ~ v3_pre_topc(B_104,A_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_428,plain,(
    ! [B_104] :
      ( r1_tarski(B_104,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_104,'#skF_3')
      | ~ v3_pre_topc(B_104,'#skF_1')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_421])).

tff(c_477,plain,(
    ! [B_112] :
      ( r1_tarski(B_112,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_112,'#skF_3')
      | ~ v3_pre_topc(B_112,'#skF_1')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_428])).

tff(c_641,plain,(
    ! [A_119] :
      ( r1_tarski(A_119,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_119,'#skF_3')
      | ~ v3_pre_topc(A_119,'#skF_1')
      | ~ r1_tarski(A_119,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8,c_477])).

tff(c_480,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_477])).

tff(c_490,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_63,c_480])).

tff(c_114,plain,(
    ! [C_64,A_65,B_66] :
      ( r2_hidden(C_64,A_65)
      | ~ r2_hidden(C_64,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_118,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_2',A_67)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_131,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_2',B_68)
      | ~ r1_tarski('#skF_4',B_68) ) ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_4,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_182,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2',A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73))
      | ~ r1_tarski('#skF_4',B_74) ) ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_194,plain,(
    ! [B_9,A_8] :
      ( r2_hidden('#skF_2',B_9)
      | ~ r1_tarski('#skF_4',A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_8,c_182])).

tff(c_515,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_2',B_9)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_9) ) ),
    inference(resolution,[status(thm)],[c_490,c_194])).

tff(c_645,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_641,c_515])).

tff(c_671,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_233,c_645])).

tff(c_747,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_671])).

tff(c_759,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_747])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_759])).

tff(c_771,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_16,plain,(
    ! [C_28,A_22,B_26] :
      ( m1_connsp_2(C_28,A_22,B_26)
      | ~ r2_hidden(B_26,k1_tops_1(A_22,C_28))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_774,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_771,c_16])).

tff(c_779,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_774])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_289,c_779])).

tff(c_882,plain,(
    ! [D_131] :
      ( ~ r2_hidden('#skF_2',D_131)
      | ~ r1_tarski(D_131,'#skF_3')
      | ~ v3_pre_topc(D_131,'#skF_1')
      | ~ m1_subset_1(D_131,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_885,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_882])).

tff(c_896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_63,c_62,c_885])).

tff(c_898,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_902,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_898])).

tff(c_911,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_908,c_902])).

tff(c_917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_911])).

tff(c_918,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_966,plain,(
    ! [A_149,B_150] :
      ( r1_tarski(k1_tops_1(A_149,B_150),B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_971,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_966])).

tff(c_975,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_971])).

tff(c_1431,plain,(
    ! [B_204,A_205,C_206] :
      ( r2_hidden(B_204,k1_tops_1(A_205,C_206))
      | ~ m1_connsp_2(C_206,A_205,B_204)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_subset_1(B_204,u1_struct_0(A_205))
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1436,plain,(
    ! [B_204] :
      ( r2_hidden(B_204,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_204)
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_1431])).

tff(c_1440,plain,(
    ! [B_204] :
      ( r2_hidden(B_204,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_204)
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1436])).

tff(c_1446,plain,(
    ! [B_207] :
      ( r2_hidden(B_207,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_207)
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1440])).

tff(c_976,plain,(
    ! [A_151,B_152] :
      ( v3_pre_topc(k1_tops_1(A_151,B_152),A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_982,plain,(
    ! [A_151,A_8] :
      ( v3_pre_topc(k1_tops_1(A_151,A_8),A_151)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | ~ r1_tarski(A_8,u1_struct_0(A_151)) ) ),
    inference(resolution,[status(thm)],[c_8,c_976])).

tff(c_920,plain,(
    ! [A_134,C_135,B_136] :
      ( r1_tarski(A_134,C_135)
      | ~ r1_tarski(B_136,C_135)
      | ~ r1_tarski(A_134,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_923,plain,(
    ! [A_134] :
      ( r1_tarski(A_134,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_134,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_61,c_920])).

tff(c_919,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [D_51] :
      ( ~ r2_hidden('#skF_2',D_51)
      | ~ r1_tarski(D_51,'#skF_3')
      | ~ v3_pre_topc(D_51,'#skF_1')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_994,plain,(
    ! [D_154] :
      ( ~ r2_hidden('#skF_2',D_154)
      | ~ r1_tarski(D_154,'#skF_3')
      | ~ v3_pre_topc(D_154,'#skF_1')
      | ~ m1_subset_1(D_154,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_919,c_40])).

tff(c_1020,plain,(
    ! [A_159] :
      ( ~ r2_hidden('#skF_2',A_159)
      | ~ r1_tarski(A_159,'#skF_3')
      | ~ v3_pre_topc(A_159,'#skF_1')
      | ~ r1_tarski(A_159,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8,c_994])).

tff(c_1034,plain,(
    ! [A_160] :
      ( ~ r2_hidden('#skF_2',A_160)
      | ~ v3_pre_topc(A_160,'#skF_1')
      | ~ r1_tarski(A_160,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_923,c_1020])).

tff(c_1038,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_8),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_982,c_1034])).

tff(c_1047,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_8),'#skF_3')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1038])).

tff(c_1452,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1446,c_1047])).

tff(c_1465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_918,c_61,c_975,c_1452])).

tff(c_1466,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1527,plain,(
    ! [A_221,B_222] :
      ( r1_tarski(k1_tops_1(A_221,B_222),B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1532,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1527])).

tff(c_1536,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1532])).

tff(c_1716,plain,(
    ! [B_258,A_259,C_260] :
      ( r2_hidden(B_258,k1_tops_1(A_259,C_260))
      | ~ m1_connsp_2(C_260,A_259,B_258)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ m1_subset_1(B_258,u1_struct_0(A_259))
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1721,plain,(
    ! [B_258] :
      ( r2_hidden(B_258,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_258)
      | ~ m1_subset_1(B_258,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_1716])).

tff(c_1725,plain,(
    ! [B_258] :
      ( r2_hidden(B_258,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_258)
      | ~ m1_subset_1(B_258,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1721])).

tff(c_1727,plain,(
    ! [B_261] :
      ( r2_hidden(B_261,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_261)
      | ~ m1_subset_1(B_261,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1725])).

tff(c_1569,plain,(
    ! [A_226,B_227] :
      ( v3_pre_topc(k1_tops_1(A_226,B_227),A_226)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1575,plain,(
    ! [A_226,A_8] :
      ( v3_pre_topc(k1_tops_1(A_226,A_8),A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | ~ r1_tarski(A_8,u1_struct_0(A_226)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1569])).

tff(c_1470,plain,(
    ! [A_208,C_209,B_210] :
      ( r1_tarski(A_208,C_209)
      | ~ r1_tarski(B_210,C_209)
      | ~ r1_tarski(A_208,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1475,plain,(
    ! [A_208] :
      ( r1_tarski(A_208,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_208,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_61,c_1470])).

tff(c_1467,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,(
    ! [D_51] :
      ( ~ r2_hidden('#skF_2',D_51)
      | ~ r1_tarski(D_51,'#skF_3')
      | ~ v3_pre_topc(D_51,'#skF_1')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1501,plain,(
    ! [D_218] :
      ( ~ r2_hidden('#skF_2',D_218)
      | ~ r1_tarski(D_218,'#skF_3')
      | ~ v3_pre_topc(D_218,'#skF_1')
      | ~ m1_subset_1(D_218,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1467,c_36])).

tff(c_1580,plain,(
    ! [A_230] :
      ( ~ r2_hidden('#skF_2',A_230)
      | ~ r1_tarski(A_230,'#skF_3')
      | ~ v3_pre_topc(A_230,'#skF_1')
      | ~ r1_tarski(A_230,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8,c_1501])).

tff(c_1595,plain,(
    ! [A_231] :
      ( ~ r2_hidden('#skF_2',A_231)
      | ~ v3_pre_topc(A_231,'#skF_1')
      | ~ r1_tarski(A_231,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1475,c_1580])).

tff(c_1599,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_8),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1575,c_1595])).

tff(c_1608,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_8),'#skF_3')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1599])).

tff(c_1731,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1727,c_1608])).

tff(c_1740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1466,c_61,c_1536,c_1731])).

tff(c_1741,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1744,plain,(
    ! [A_262,B_263] :
      ( r1_tarski(A_262,B_263)
      | ~ m1_subset_1(A_262,k1_zfmisc_1(B_263)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1748,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_1744])).

tff(c_1785,plain,(
    ! [A_276,B_277] :
      ( r1_tarski(k1_tops_1(A_276,B_277),B_277)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1790,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1785])).

tff(c_1794,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1790])).

tff(c_2006,plain,(
    ! [B_315,A_316,C_317] :
      ( r2_hidden(B_315,k1_tops_1(A_316,C_317))
      | ~ m1_connsp_2(C_317,A_316,B_315)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ m1_subset_1(B_315,u1_struct_0(A_316))
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2011,plain,(
    ! [B_315] :
      ( r2_hidden(B_315,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_315)
      | ~ m1_subset_1(B_315,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_2006])).

tff(c_2015,plain,(
    ! [B_315] :
      ( r2_hidden(B_315,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_315)
      | ~ m1_subset_1(B_315,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2011])).

tff(c_2017,plain,(
    ! [B_318] :
      ( r2_hidden(B_318,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_318)
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2015])).

tff(c_1802,plain,(
    ! [A_279,B_280] :
      ( v3_pre_topc(k1_tops_1(A_279,B_280),A_279)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1846,plain,(
    ! [A_285,A_286] :
      ( v3_pre_topc(k1_tops_1(A_285,A_286),A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | ~ r1_tarski(A_286,u1_struct_0(A_285)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1802])).

tff(c_1755,plain,(
    ! [A_266,C_267,B_268] :
      ( r1_tarski(A_266,C_267)
      | ~ r1_tarski(B_268,C_267)
      | ~ r1_tarski(A_266,B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1758,plain,(
    ! [A_266] :
      ( r1_tarski(A_266,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_266,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1748,c_1755])).

tff(c_1742,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_51] :
      ( ~ r2_hidden('#skF_2',D_51)
      | ~ r1_tarski(D_51,'#skF_3')
      | ~ v3_pre_topc(D_51,'#skF_1')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1774,plain,(
    ! [D_275] :
      ( ~ r2_hidden('#skF_2',D_275)
      | ~ r1_tarski(D_275,'#skF_3')
      | ~ v3_pre_topc(D_275,'#skF_1')
      | ~ m1_subset_1(D_275,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1742,c_44])).

tff(c_1825,plain,(
    ! [A_283] :
      ( ~ r2_hidden('#skF_2',A_283)
      | ~ r1_tarski(A_283,'#skF_3')
      | ~ v3_pre_topc(A_283,'#skF_1')
      | ~ r1_tarski(A_283,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8,c_1774])).

tff(c_1837,plain,(
    ! [A_266] :
      ( ~ r2_hidden('#skF_2',A_266)
      | ~ v3_pre_topc(A_266,'#skF_1')
      | ~ r1_tarski(A_266,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1758,c_1825])).

tff(c_1850,plain,(
    ! [A_286] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_286))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_286),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_286,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1846,c_1837])).

tff(c_1853,plain,(
    ! [A_286] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_286))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_286),'#skF_3')
      | ~ r1_tarski(A_286,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1850])).

tff(c_2021,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2017,c_1853])).

tff(c_2030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1741,c_1748,c_1794,c_2021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.72  
% 4.14/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.73  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.14/1.73  
% 4.14/1.73  %Foreground sorts:
% 4.14/1.73  
% 4.14/1.73  
% 4.14/1.73  %Background operators:
% 4.14/1.73  
% 4.14/1.73  
% 4.14/1.73  %Foreground operators:
% 4.14/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.14/1.73  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.14/1.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.14/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.14/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.73  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.14/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.14/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.14/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.14/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.14/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.14/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.73  
% 4.14/1.77  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.14/1.77  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.14/1.77  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.14/1.77  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.14/1.77  tff(f_50, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.14/1.77  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.14/1.77  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.14/1.77  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.14/1.77  tff(c_24, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_42, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_63, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 4.14/1.77  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_53, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.14/1.77  tff(c_61, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_53])).
% 4.14/1.77  tff(c_64, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.77  tff(c_908, plain, (![A_133]: (r1_tarski(A_133, u1_struct_0('#skF_1')) | ~r1_tarski(A_133, '#skF_3'))), inference(resolution, [status(thm)], [c_61, c_64])).
% 4.14/1.77  tff(c_8, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.14/1.77  tff(c_46, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_51, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.14/1.77  tff(c_38, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_62, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 4.14/1.77  tff(c_50, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_71, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_50])).
% 4.14/1.77  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_32, plain, (![D_51]: (~r2_hidden('#skF_2', D_51) | ~r1_tarski(D_51, '#skF_3') | ~v3_pre_topc(D_51, '#skF_1') | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_289, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_32])).
% 4.14/1.77  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_219, plain, (![A_77, B_78]: (r1_tarski(k1_tops_1(A_77, B_78), B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.14/1.77  tff(c_226, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_219])).
% 4.14/1.77  tff(c_233, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_226])).
% 4.14/1.77  tff(c_70, plain, (![A_56]: (r1_tarski(A_56, u1_struct_0('#skF_1')) | ~r1_tarski(A_56, '#skF_3'))), inference(resolution, [status(thm)], [c_61, c_64])).
% 4.14/1.77  tff(c_273, plain, (![A_82, B_83]: (v3_pre_topc(k1_tops_1(A_82, B_83), A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.14/1.77  tff(c_280, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_273])).
% 4.14/1.77  tff(c_287, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_280])).
% 4.14/1.77  tff(c_421, plain, (![B_104, A_105, C_106]: (r1_tarski(B_104, k1_tops_1(A_105, C_106)) | ~r1_tarski(B_104, C_106) | ~v3_pre_topc(B_104, A_105) | ~m1_subset_1(C_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.14/1.77  tff(c_428, plain, (![B_104]: (r1_tarski(B_104, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_104, '#skF_3') | ~v3_pre_topc(B_104, '#skF_1') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_421])).
% 4.14/1.77  tff(c_477, plain, (![B_112]: (r1_tarski(B_112, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_112, '#skF_3') | ~v3_pre_topc(B_112, '#skF_1') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_428])).
% 4.14/1.77  tff(c_641, plain, (![A_119]: (r1_tarski(A_119, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_119, '#skF_3') | ~v3_pre_topc(A_119, '#skF_1') | ~r1_tarski(A_119, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_477])).
% 4.14/1.77  tff(c_480, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_71, c_477])).
% 4.14/1.77  tff(c_490, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_63, c_480])).
% 4.14/1.77  tff(c_114, plain, (![C_64, A_65, B_66]: (r2_hidden(C_64, A_65) | ~r2_hidden(C_64, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.14/1.77  tff(c_118, plain, (![A_67]: (r2_hidden('#skF_2', A_67) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_62, c_114])).
% 4.14/1.77  tff(c_131, plain, (![B_68]: (r2_hidden('#skF_2', B_68) | ~r1_tarski('#skF_4', B_68))), inference(resolution, [status(thm)], [c_8, c_118])).
% 4.14/1.77  tff(c_4, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.14/1.77  tff(c_182, plain, (![A_73, B_74]: (r2_hidden('#skF_2', A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)) | ~r1_tarski('#skF_4', B_74))), inference(resolution, [status(thm)], [c_131, c_4])).
% 4.14/1.77  tff(c_194, plain, (![B_9, A_8]: (r2_hidden('#skF_2', B_9) | ~r1_tarski('#skF_4', A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_8, c_182])).
% 4.14/1.77  tff(c_515, plain, (![B_9]: (r2_hidden('#skF_2', B_9) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_9))), inference(resolution, [status(thm)], [c_490, c_194])).
% 4.14/1.77  tff(c_645, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_641, c_515])).
% 4.14/1.77  tff(c_671, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_233, c_645])).
% 4.14/1.77  tff(c_747, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_671])).
% 4.14/1.77  tff(c_759, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_70, c_747])).
% 4.14/1.77  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_759])).
% 4.14/1.77  tff(c_771, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_671])).
% 4.14/1.77  tff(c_16, plain, (![C_28, A_22, B_26]: (m1_connsp_2(C_28, A_22, B_26) | ~r2_hidden(B_26, k1_tops_1(A_22, C_28)) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.14/1.77  tff(c_774, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_771, c_16])).
% 4.14/1.77  tff(c_779, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_774])).
% 4.14/1.77  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_289, c_779])).
% 4.14/1.77  tff(c_882, plain, (![D_131]: (~r2_hidden('#skF_2', D_131) | ~r1_tarski(D_131, '#skF_3') | ~v3_pre_topc(D_131, '#skF_1') | ~m1_subset_1(D_131, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_32])).
% 4.14/1.77  tff(c_885, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_71, c_882])).
% 4.14/1.77  tff(c_896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_63, c_62, c_885])).
% 4.14/1.77  tff(c_898, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 4.14/1.77  tff(c_902, plain, (~r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_898])).
% 4.14/1.77  tff(c_911, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_908, c_902])).
% 4.14/1.77  tff(c_917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_911])).
% 4.14/1.77  tff(c_918, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.14/1.77  tff(c_966, plain, (![A_149, B_150]: (r1_tarski(k1_tops_1(A_149, B_150), B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.14/1.77  tff(c_971, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_966])).
% 4.14/1.77  tff(c_975, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_971])).
% 4.14/1.77  tff(c_1431, plain, (![B_204, A_205, C_206]: (r2_hidden(B_204, k1_tops_1(A_205, C_206)) | ~m1_connsp_2(C_206, A_205, B_204) | ~m1_subset_1(C_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_subset_1(B_204, u1_struct_0(A_205)) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.14/1.77  tff(c_1436, plain, (![B_204]: (r2_hidden(B_204, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_204) | ~m1_subset_1(B_204, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_1431])).
% 4.14/1.77  tff(c_1440, plain, (![B_204]: (r2_hidden(B_204, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_204) | ~m1_subset_1(B_204, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1436])).
% 4.14/1.77  tff(c_1446, plain, (![B_207]: (r2_hidden(B_207, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_207) | ~m1_subset_1(B_207, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_1440])).
% 4.14/1.77  tff(c_976, plain, (![A_151, B_152]: (v3_pre_topc(k1_tops_1(A_151, B_152), A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.14/1.77  tff(c_982, plain, (![A_151, A_8]: (v3_pre_topc(k1_tops_1(A_151, A_8), A_151) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | ~r1_tarski(A_8, u1_struct_0(A_151)))), inference(resolution, [status(thm)], [c_8, c_976])).
% 4.14/1.77  tff(c_920, plain, (![A_134, C_135, B_136]: (r1_tarski(A_134, C_135) | ~r1_tarski(B_136, C_135) | ~r1_tarski(A_134, B_136))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.77  tff(c_923, plain, (![A_134]: (r1_tarski(A_134, u1_struct_0('#skF_1')) | ~r1_tarski(A_134, '#skF_3'))), inference(resolution, [status(thm)], [c_61, c_920])).
% 4.14/1.77  tff(c_919, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 4.14/1.77  tff(c_40, plain, (![D_51]: (~r2_hidden('#skF_2', D_51) | ~r1_tarski(D_51, '#skF_3') | ~v3_pre_topc(D_51, '#skF_1') | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_994, plain, (![D_154]: (~r2_hidden('#skF_2', D_154) | ~r1_tarski(D_154, '#skF_3') | ~v3_pre_topc(D_154, '#skF_1') | ~m1_subset_1(D_154, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_919, c_40])).
% 4.14/1.77  tff(c_1020, plain, (![A_159]: (~r2_hidden('#skF_2', A_159) | ~r1_tarski(A_159, '#skF_3') | ~v3_pre_topc(A_159, '#skF_1') | ~r1_tarski(A_159, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_994])).
% 4.14/1.77  tff(c_1034, plain, (![A_160]: (~r2_hidden('#skF_2', A_160) | ~v3_pre_topc(A_160, '#skF_1') | ~r1_tarski(A_160, '#skF_3'))), inference(resolution, [status(thm)], [c_923, c_1020])).
% 4.14/1.77  tff(c_1038, plain, (![A_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_8)) | ~r1_tarski(k1_tops_1('#skF_1', A_8), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_8, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_982, c_1034])).
% 4.14/1.77  tff(c_1047, plain, (![A_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_8)) | ~r1_tarski(k1_tops_1('#skF_1', A_8), '#skF_3') | ~r1_tarski(A_8, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1038])).
% 4.14/1.77  tff(c_1452, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1446, c_1047])).
% 4.14/1.77  tff(c_1465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_918, c_61, c_975, c_1452])).
% 4.14/1.77  tff(c_1466, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 4.14/1.77  tff(c_1527, plain, (![A_221, B_222]: (r1_tarski(k1_tops_1(A_221, B_222), B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.14/1.77  tff(c_1532, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1527])).
% 4.14/1.77  tff(c_1536, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1532])).
% 4.14/1.77  tff(c_1716, plain, (![B_258, A_259, C_260]: (r2_hidden(B_258, k1_tops_1(A_259, C_260)) | ~m1_connsp_2(C_260, A_259, B_258) | ~m1_subset_1(C_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~m1_subset_1(B_258, u1_struct_0(A_259)) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.14/1.77  tff(c_1721, plain, (![B_258]: (r2_hidden(B_258, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_258) | ~m1_subset_1(B_258, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_1716])).
% 4.14/1.77  tff(c_1725, plain, (![B_258]: (r2_hidden(B_258, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_258) | ~m1_subset_1(B_258, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1721])).
% 4.14/1.77  tff(c_1727, plain, (![B_261]: (r2_hidden(B_261, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_261) | ~m1_subset_1(B_261, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_1725])).
% 4.14/1.77  tff(c_1569, plain, (![A_226, B_227]: (v3_pre_topc(k1_tops_1(A_226, B_227), A_226) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.14/1.77  tff(c_1575, plain, (![A_226, A_8]: (v3_pre_topc(k1_tops_1(A_226, A_8), A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | ~r1_tarski(A_8, u1_struct_0(A_226)))), inference(resolution, [status(thm)], [c_8, c_1569])).
% 4.14/1.77  tff(c_1470, plain, (![A_208, C_209, B_210]: (r1_tarski(A_208, C_209) | ~r1_tarski(B_210, C_209) | ~r1_tarski(A_208, B_210))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.77  tff(c_1475, plain, (![A_208]: (r1_tarski(A_208, u1_struct_0('#skF_1')) | ~r1_tarski(A_208, '#skF_3'))), inference(resolution, [status(thm)], [c_61, c_1470])).
% 4.14/1.77  tff(c_1467, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 4.14/1.77  tff(c_36, plain, (![D_51]: (~r2_hidden('#skF_2', D_51) | ~r1_tarski(D_51, '#skF_3') | ~v3_pre_topc(D_51, '#skF_1') | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_1501, plain, (![D_218]: (~r2_hidden('#skF_2', D_218) | ~r1_tarski(D_218, '#skF_3') | ~v3_pre_topc(D_218, '#skF_1') | ~m1_subset_1(D_218, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1467, c_36])).
% 4.14/1.77  tff(c_1580, plain, (![A_230]: (~r2_hidden('#skF_2', A_230) | ~r1_tarski(A_230, '#skF_3') | ~v3_pre_topc(A_230, '#skF_1') | ~r1_tarski(A_230, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1501])).
% 4.14/1.77  tff(c_1595, plain, (![A_231]: (~r2_hidden('#skF_2', A_231) | ~v3_pre_topc(A_231, '#skF_1') | ~r1_tarski(A_231, '#skF_3'))), inference(resolution, [status(thm)], [c_1475, c_1580])).
% 4.14/1.77  tff(c_1599, plain, (![A_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_8)) | ~r1_tarski(k1_tops_1('#skF_1', A_8), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_8, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1575, c_1595])).
% 4.14/1.77  tff(c_1608, plain, (![A_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_8)) | ~r1_tarski(k1_tops_1('#skF_1', A_8), '#skF_3') | ~r1_tarski(A_8, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1599])).
% 4.14/1.77  tff(c_1731, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1727, c_1608])).
% 4.14/1.77  tff(c_1740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1466, c_61, c_1536, c_1731])).
% 4.14/1.77  tff(c_1741, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.14/1.77  tff(c_1744, plain, (![A_262, B_263]: (r1_tarski(A_262, B_263) | ~m1_subset_1(A_262, k1_zfmisc_1(B_263)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.14/1.77  tff(c_1748, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_1744])).
% 4.14/1.77  tff(c_1785, plain, (![A_276, B_277]: (r1_tarski(k1_tops_1(A_276, B_277), B_277) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.14/1.77  tff(c_1790, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1785])).
% 4.14/1.77  tff(c_1794, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1790])).
% 4.14/1.77  tff(c_2006, plain, (![B_315, A_316, C_317]: (r2_hidden(B_315, k1_tops_1(A_316, C_317)) | ~m1_connsp_2(C_317, A_316, B_315) | ~m1_subset_1(C_317, k1_zfmisc_1(u1_struct_0(A_316))) | ~m1_subset_1(B_315, u1_struct_0(A_316)) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.14/1.77  tff(c_2011, plain, (![B_315]: (r2_hidden(B_315, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_315) | ~m1_subset_1(B_315, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_2006])).
% 4.14/1.77  tff(c_2015, plain, (![B_315]: (r2_hidden(B_315, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_315) | ~m1_subset_1(B_315, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2011])).
% 4.14/1.77  tff(c_2017, plain, (![B_318]: (r2_hidden(B_318, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_318) | ~m1_subset_1(B_318, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_2015])).
% 4.14/1.77  tff(c_1802, plain, (![A_279, B_280]: (v3_pre_topc(k1_tops_1(A_279, B_280), A_279) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.14/1.77  tff(c_1846, plain, (![A_285, A_286]: (v3_pre_topc(k1_tops_1(A_285, A_286), A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | ~r1_tarski(A_286, u1_struct_0(A_285)))), inference(resolution, [status(thm)], [c_8, c_1802])).
% 4.14/1.77  tff(c_1755, plain, (![A_266, C_267, B_268]: (r1_tarski(A_266, C_267) | ~r1_tarski(B_268, C_267) | ~r1_tarski(A_266, B_268))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.77  tff(c_1758, plain, (![A_266]: (r1_tarski(A_266, u1_struct_0('#skF_1')) | ~r1_tarski(A_266, '#skF_3'))), inference(resolution, [status(thm)], [c_1748, c_1755])).
% 4.14/1.77  tff(c_1742, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.14/1.77  tff(c_44, plain, (![D_51]: (~r2_hidden('#skF_2', D_51) | ~r1_tarski(D_51, '#skF_3') | ~v3_pre_topc(D_51, '#skF_1') | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.14/1.77  tff(c_1774, plain, (![D_275]: (~r2_hidden('#skF_2', D_275) | ~r1_tarski(D_275, '#skF_3') | ~v3_pre_topc(D_275, '#skF_1') | ~m1_subset_1(D_275, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1742, c_44])).
% 4.14/1.77  tff(c_1825, plain, (![A_283]: (~r2_hidden('#skF_2', A_283) | ~r1_tarski(A_283, '#skF_3') | ~v3_pre_topc(A_283, '#skF_1') | ~r1_tarski(A_283, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1774])).
% 4.14/1.77  tff(c_1837, plain, (![A_266]: (~r2_hidden('#skF_2', A_266) | ~v3_pre_topc(A_266, '#skF_1') | ~r1_tarski(A_266, '#skF_3'))), inference(resolution, [status(thm)], [c_1758, c_1825])).
% 4.14/1.77  tff(c_1850, plain, (![A_286]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_286)) | ~r1_tarski(k1_tops_1('#skF_1', A_286), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_286, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1846, c_1837])).
% 4.14/1.77  tff(c_1853, plain, (![A_286]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_286)) | ~r1_tarski(k1_tops_1('#skF_1', A_286), '#skF_3') | ~r1_tarski(A_286, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1850])).
% 4.14/1.77  tff(c_2021, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2017, c_1853])).
% 4.14/1.77  tff(c_2030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1741, c_1748, c_1794, c_2021])).
% 4.14/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.77  
% 4.14/1.77  Inference rules
% 4.14/1.77  ----------------------
% 4.14/1.77  #Ref     : 0
% 4.14/1.77  #Sup     : 434
% 4.14/1.77  #Fact    : 0
% 4.14/1.77  #Define  : 0
% 4.14/1.77  #Split   : 22
% 4.14/1.77  #Chain   : 0
% 4.14/1.77  #Close   : 0
% 4.14/1.77  
% 4.14/1.77  Ordering : KBO
% 4.14/1.77  
% 4.14/1.77  Simplification rules
% 4.14/1.77  ----------------------
% 4.14/1.77  #Subsume      : 170
% 4.14/1.77  #Demod        : 220
% 4.14/1.77  #Tautology    : 55
% 4.14/1.77  #SimpNegUnit  : 11
% 4.14/1.77  #BackRed      : 0
% 4.14/1.77  
% 4.14/1.77  #Partial instantiations: 0
% 4.14/1.77  #Strategies tried      : 1
% 4.14/1.77  
% 4.14/1.77  Timing (in seconds)
% 4.14/1.77  ----------------------
% 4.14/1.77  Preprocessing        : 0.31
% 4.14/1.77  Parsing              : 0.17
% 4.14/1.77  CNF conversion       : 0.03
% 4.14/1.77  Main loop            : 0.66
% 4.14/1.77  Inferencing          : 0.23
% 4.14/1.77  Reduction            : 0.19
% 4.14/1.77  Demodulation         : 0.13
% 4.14/1.77  BG Simplification    : 0.03
% 4.14/1.77  Subsumption          : 0.17
% 4.14/1.77  Abstraction          : 0.03
% 4.14/1.77  MUC search           : 0.00
% 4.14/1.77  Cooper               : 0.00
% 4.14/1.77  Total                : 1.04
% 4.14/1.77  Index Insertion      : 0.00
% 4.14/1.77  Index Deletion       : 0.00
% 4.14/1.77  Index Matching       : 0.00
% 4.14/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
