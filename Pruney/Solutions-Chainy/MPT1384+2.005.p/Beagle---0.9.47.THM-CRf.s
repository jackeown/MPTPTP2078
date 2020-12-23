%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:14 EST 2020

% Result     : Theorem 17.87s
% Output     : CNFRefutation 17.96s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 445 expanded)
%              Number of leaves         :   30 ( 163 expanded)
%              Depth                    :   32
%              Number of atoms          :  450 (1895 expanded)
%              Number of equality atoms :   19 (  67 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1 > #skF_6

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( m1_connsp_2(D,A,C)
                              & r1_tarski(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_121,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_104,axiom,(
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

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_48,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_79,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_113,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(k1_tops_1(A_95,B_96),B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_115,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_113])).

tff(c_118,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_115])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_121,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_122,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_156,plain,(
    ! [A_108,B_109] :
      ( k1_tops_1(A_108,k1_tops_1(A_108,B_109)) = k1_tops_1(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_160,plain,
    ( k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_156])).

tff(c_164,plain,(
    k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_160])).

tff(c_710,plain,(
    ! [C_176,A_177,B_178] :
      ( m1_connsp_2(C_176,A_177,B_178)
      | ~ r2_hidden(B_178,k1_tops_1(A_177,C_176))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ m1_subset_1(B_178,u1_struct_0(A_177))
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_731,plain,(
    ! [B_178] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_4'),'#skF_3',B_178)
      | ~ r2_hidden(B_178,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_178,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_710])).

tff(c_750,plain,(
    ! [B_178] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_4'),'#skF_3',B_178)
      | ~ r2_hidden(B_178,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_178,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_731])).

tff(c_751,plain,(
    ! [B_178] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_4'),'#skF_3',B_178)
      | ~ r2_hidden(B_178,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_178,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_750])).

tff(c_778,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_781,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_778])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_781])).

tff(c_787,plain,(
    m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_16,plain,(
    ! [A_8,B_9,C_13] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_13),B_9)
      | r1_tarski(B_9,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_8,B_9,C_13] :
      ( m1_subset_1('#skF_2'(A_8,B_9,C_13),A_8)
      | r1_tarski(B_9,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [C_79] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | m1_subset_1('#skF_6'(C_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_194,plain,(
    ! [C_79] :
      ( m1_subset_1('#skF_6'(C_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_76])).

tff(c_68,plain,(
    ! [C_79] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | m1_connsp_2('#skF_6'(C_79),'#skF_3',C_79)
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_154,plain,(
    ! [C_79] :
      ( m1_connsp_2('#skF_6'(C_79),'#skF_3',C_79)
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_68])).

tff(c_60,plain,(
    ! [C_79] :
      ( v3_pre_topc('#skF_4','#skF_3')
      | r1_tarski('#skF_6'(C_79),'#skF_4')
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_87,plain,(
    ! [C_79] :
      ( r1_tarski('#skF_6'(C_79),'#skF_4')
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_60])).

tff(c_26,plain,(
    ! [A_22,B_26,C_28] :
      ( r1_tarski(k1_tops_1(A_22,B_26),k1_tops_1(A_22,C_28))
      | ~ r1_tarski(B_26,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_311,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_tarski(k1_tops_1(A_132,B_133),k1_tops_1(A_132,C_134))
      | ~ r1_tarski(B_133,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_330,plain,(
    ! [C_134] :
      ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),k1_tops_1('#skF_3',C_134))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_311])).

tff(c_345,plain,(
    ! [C_134] :
      ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),k1_tops_1('#skF_3',C_134))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_330])).

tff(c_1884,plain,(
    ! [C_261] :
      ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),k1_tops_1('#skF_3',C_261))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_345])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_92,B_93,B_2,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_2)
      | ~ r1_tarski(B_94,B_2)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_2519,plain,(
    ! [A_313,B_314,C_315] :
      ( r2_hidden('#skF_1'(A_313,B_314),k1_tops_1('#skF_3',C_315))
      | ~ r1_tarski(A_313,k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(A_313,B_314)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_1884,c_111])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2557,plain,(
    ! [A_316,C_317] :
      ( ~ r1_tarski(A_316,k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(A_316,k1_tops_1('#skF_3',C_317))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_2519,c_4])).

tff(c_2571,plain,(
    ! [B_26,C_317] :
      ( r1_tarski(k1_tops_1('#skF_3',B_26),k1_tops_1('#skF_3',C_317))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(B_26,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_2557])).

tff(c_3218,plain,(
    ! [B_360,C_361] :
      ( r1_tarski(k1_tops_1('#skF_3',B_360),k1_tops_1('#skF_3',C_361))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),C_361)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(B_360,'#skF_4')
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2571])).

tff(c_3323,plain,(
    ! [B_360] :
      ( r1_tarski(k1_tops_1('#skF_3',B_360),k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(B_360,'#skF_4')
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_3218])).

tff(c_3380,plain,(
    ! [B_362] :
      ( r1_tarski(k1_tops_1('#skF_3',B_362),k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski(B_362,'#skF_4')
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_12,c_3323])).

tff(c_3695,plain,(
    ! [A_375,B_376,B_377] :
      ( r2_hidden('#skF_1'(A_375,B_376),k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_375,k1_tops_1('#skF_3',B_377))
      | r1_tarski(A_375,B_376)
      | ~ r1_tarski(B_377,'#skF_4')
      | ~ m1_subset_1(B_377,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_3380,c_111])).

tff(c_3720,plain,(
    ! [B_26,B_376,C_28] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3',B_26),B_376),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3',B_26),B_376)
      | ~ r1_tarski(C_28,'#skF_4')
      | ~ r1_tarski(B_26,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_3695])).

tff(c_33502,plain,(
    ! [B_1089,B_1090,C_1091] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3',B_1089),B_1090),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3',B_1089),B_1090)
      | ~ r1_tarski(C_1091,'#skF_4')
      | ~ r1_tarski(B_1089,C_1091)
      | ~ m1_subset_1(C_1091,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_1089,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3720])).

tff(c_33592,plain,(
    ! [C_79,B_1090] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_6'(C_79)),B_1090),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_6'(C_79)),B_1090)
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_6'(C_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_87,c_33502])).

tff(c_33673,plain,(
    ! [C_1092,B_1093] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_6'(C_1092)),B_1093),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_6'(C_1092)),B_1093)
      | ~ m1_subset_1('#skF_6'(C_1092),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_1092,'#skF_4')
      | ~ m1_subset_1(C_1092,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12,c_33592])).

tff(c_33698,plain,(
    ! [C_1094] :
      ( r1_tarski(k1_tops_1('#skF_3','#skF_6'(C_1094)),k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_6'(C_1094),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_1094,'#skF_4')
      | ~ m1_subset_1(C_1094,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_33673,c_4])).

tff(c_843,plain,(
    ! [B_187,A_188,C_189] :
      ( r2_hidden(B_187,k1_tops_1(A_188,C_189))
      | ~ m1_connsp_2(C_189,A_188,B_187)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_187,u1_struct_0(A_188))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_850,plain,(
    ! [B_187,C_79] :
      ( r2_hidden(B_187,k1_tops_1('#skF_3','#skF_6'(C_79)))
      | ~ m1_connsp_2('#skF_6'(C_79),'#skF_3',B_187)
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_194,c_843])).

tff(c_862,plain,(
    ! [B_187,C_79] :
      ( r2_hidden(B_187,k1_tops_1('#skF_3','#skF_6'(C_79)))
      | ~ m1_connsp_2('#skF_6'(C_79),'#skF_3',B_187)
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_79,'#skF_4')
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_850])).

tff(c_908,plain,(
    ! [B_194,C_195] :
      ( r2_hidden(B_194,k1_tops_1('#skF_3','#skF_6'(C_195)))
      | ~ m1_connsp_2('#skF_6'(C_195),'#skF_3',B_194)
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_3'))
      | ~ r2_hidden(C_195,'#skF_4')
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_862])).

tff(c_926,plain,(
    ! [B_194,B_2,C_195] :
      ( r2_hidden(B_194,B_2)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_6'(C_195)),B_2)
      | ~ m1_connsp_2('#skF_6'(C_195),'#skF_3',B_194)
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_3'))
      | ~ r2_hidden(C_195,'#skF_4')
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_908,c_2])).

tff(c_34083,plain,(
    ! [B_1101,C_1102] :
      ( r2_hidden(B_1101,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_6'(C_1102),'#skF_3',B_1101)
      | ~ m1_subset_1(B_1101,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6'(C_1102),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_1102,'#skF_4')
      | ~ m1_subset_1(C_1102,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_33698,c_926])).

tff(c_34104,plain,(
    ! [C_1103] :
      ( r2_hidden(C_1103,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_6'(C_1103),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_1103,'#skF_4')
      | ~ m1_subset_1(C_1103,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_154,c_34083])).

tff(c_34109,plain,(
    ! [C_1104] :
      ( r2_hidden(C_1104,k1_tops_1('#skF_3','#skF_4'))
      | ~ r2_hidden(C_1104,'#skF_4')
      | ~ m1_subset_1(C_1104,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_194,c_34104])).

tff(c_32,plain,(
    ! [C_50,A_44,B_48] :
      ( m1_connsp_2(C_50,A_44,B_48)
      | ~ r2_hidden(B_48,k1_tops_1(A_44,C_50))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_48,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34121,plain,(
    ! [C_1104] :
      ( m1_connsp_2('#skF_4','#skF_3',C_1104)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_1104,'#skF_4')
      | ~ m1_subset_1(C_1104,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34109,c_32])).

tff(c_34138,plain,(
    ! [C_1104] :
      ( m1_connsp_2('#skF_4','#skF_3',C_1104)
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_1104,'#skF_4')
      | ~ m1_subset_1(C_1104,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_34121])).

tff(c_34143,plain,(
    ! [C_1105] :
      ( m1_connsp_2('#skF_4','#skF_3',C_1105)
      | ~ r2_hidden(C_1105,'#skF_4')
      | ~ m1_subset_1(C_1105,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_34138])).

tff(c_35283,plain,(
    ! [B_1139,C_1140] :
      ( m1_connsp_2('#skF_4','#skF_3','#skF_2'(u1_struct_0('#skF_3'),B_1139,C_1140))
      | ~ r2_hidden('#skF_2'(u1_struct_0('#skF_3'),B_1139,C_1140),'#skF_4')
      | r1_tarski(B_1139,C_1140)
      | ~ m1_subset_1(C_1140,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_1139,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_18,c_34143])).

tff(c_854,plain,(
    ! [B_187] :
      ( r2_hidden(B_187,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_187)
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_843])).

tff(c_867,plain,(
    ! [B_187] :
      ( r2_hidden(B_187,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_187)
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_854])).

tff(c_869,plain,(
    ! [B_190] :
      ( r2_hidden(B_190,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_3',B_190)
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_867])).

tff(c_14,plain,(
    ! [A_8,B_9,C_13] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_13),C_13)
      | r1_tarski(B_9,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6188,plain,(
    ! [B_484,A_485] :
      ( r1_tarski(B_484,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(A_485))
      | ~ m1_subset_1(B_484,k1_zfmisc_1(A_485))
      | ~ m1_connsp_2('#skF_4','#skF_3','#skF_2'(A_485,B_484,k1_tops_1('#skF_3','#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_485,B_484,k1_tops_1('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_869,c_14])).

tff(c_6192,plain,(
    ! [B_9] :
      ( ~ m1_connsp_2('#skF_4','#skF_3','#skF_2'(u1_struct_0('#skF_3'),B_9,k1_tops_1('#skF_3','#skF_4')))
      | r1_tarski(B_9,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_18,c_6188])).

tff(c_6195,plain,(
    ! [B_9] :
      ( ~ m1_connsp_2('#skF_4','#skF_3','#skF_2'(u1_struct_0('#skF_3'),B_9,k1_tops_1('#skF_3','#skF_4')))
      | r1_tarski(B_9,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_6192])).

tff(c_35290,plain,(
    ! [B_1139] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_3'),B_1139,k1_tops_1('#skF_3','#skF_4')),'#skF_4')
      | r1_tarski(B_1139,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_1139,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_35283,c_6195])).

tff(c_35295,plain,(
    ! [B_1141] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_3'),B_1141,k1_tops_1('#skF_3','#skF_4')),'#skF_4')
      | r1_tarski(B_1141,k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1141,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_35290])).

tff(c_35331,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16,c_35295])).

tff(c_35358,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_787,c_35331])).

tff(c_35360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_35358])).

tff(c_35361,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_28,plain,(
    ! [C_41,A_29,D_43,B_37] :
      ( v3_pre_topc(C_41,A_29)
      | k1_tops_1(A_29,C_41) != C_41
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0(B_37)))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(B_37)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_35741,plain,(
    ! [D_1194,B_1195] :
      ( ~ m1_subset_1(D_1194,k1_zfmisc_1(u1_struct_0(B_1195)))
      | ~ l1_pre_topc(B_1195) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_35751,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_35741])).

tff(c_35759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_35751])).

tff(c_35761,plain,(
    ! [C_1196,A_1197] :
      ( v3_pre_topc(C_1196,A_1197)
      | k1_tops_1(A_1197,C_1196) != C_1196
      | ~ m1_subset_1(C_1196,k1_zfmisc_1(u1_struct_0(A_1197)))
      | ~ l1_pre_topc(A_1197)
      | ~ v2_pre_topc(A_1197) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_35774,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_35761])).

tff(c_35782,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_35361,c_35774])).

tff(c_35784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_35782])).

tff(c_35786,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_78] :
      ( ~ r1_tarski(D_78,'#skF_4')
      | ~ m1_connsp_2(D_78,'#skF_3','#skF_5')
      | ~ m1_subset_1(D_78,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_36202,plain,(
    ! [D_1270] :
      ( ~ r1_tarski(D_1270,'#skF_4')
      | ~ m1_connsp_2(D_1270,'#skF_3','#skF_5')
      | ~ m1_subset_1(D_1270,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35786,c_46])).

tff(c_36209,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_36202])).

tff(c_36215,plain,(
    ~ m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36209])).

tff(c_35785,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_35787,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_35789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35786,c_35787])).

tff(c_35790,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_30,plain,(
    ! [B_37,D_43,C_41,A_29] :
      ( k1_tops_1(B_37,D_43) = D_43
      | ~ v3_pre_topc(D_43,B_37)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0(B_37)))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(B_37)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36134,plain,(
    ! [C_1262,A_1263] :
      ( ~ m1_subset_1(C_1262,k1_zfmisc_1(u1_struct_0(A_1263)))
      | ~ l1_pre_topc(A_1263)
      | ~ v2_pre_topc(A_1263) ) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36144,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_36134])).

tff(c_36150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36144])).

tff(c_36152,plain,(
    ! [B_1264,D_1265] :
      ( k1_tops_1(B_1264,D_1265) = D_1265
      | ~ v3_pre_topc(D_1265,B_1264)
      | ~ m1_subset_1(D_1265,k1_zfmisc_1(u1_struct_0(B_1264)))
      | ~ l1_pre_topc(B_1264) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_36162,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_36152])).

tff(c_36167,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_35786,c_36162])).

tff(c_35833,plain,(
    ! [A_1213,B_1214] :
      ( r1_tarski(k1_tops_1(A_1213,B_1214),B_1214)
      | ~ m1_subset_1(B_1214,k1_zfmisc_1(u1_struct_0(A_1213)))
      | ~ l1_pre_topc(A_1213) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_35835,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_35833])).

tff(c_35838,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_35835])).

tff(c_35845,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_35838,c_8])).

tff(c_35850,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_35845])).

tff(c_36175,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36167,c_35850])).

tff(c_36179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36175])).

tff(c_36180,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_35845])).

tff(c_36772,plain,(
    ! [C_1328,A_1329,B_1330] :
      ( m1_connsp_2(C_1328,A_1329,B_1330)
      | ~ r2_hidden(B_1330,k1_tops_1(A_1329,C_1328))
      | ~ m1_subset_1(C_1328,k1_zfmisc_1(u1_struct_0(A_1329)))
      | ~ m1_subset_1(B_1330,u1_struct_0(A_1329))
      | ~ l1_pre_topc(A_1329)
      | ~ v2_pre_topc(A_1329)
      | v2_struct_0(A_1329) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36784,plain,(
    ! [B_1330] :
      ( m1_connsp_2('#skF_4','#skF_3',B_1330)
      | ~ r2_hidden(B_1330,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_1330,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36180,c_36772])).

tff(c_36801,plain,(
    ! [B_1330] :
      ( m1_connsp_2('#skF_4','#skF_3',B_1330)
      | ~ r2_hidden(B_1330,'#skF_4')
      | ~ m1_subset_1(B_1330,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36784])).

tff(c_36806,plain,(
    ! [B_1331] :
      ( m1_connsp_2('#skF_4','#skF_3',B_1331)
      | ~ r2_hidden(B_1331,'#skF_4')
      | ~ m1_subset_1(B_1331,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36801])).

tff(c_36813,plain,
    ( m1_connsp_2('#skF_4','#skF_3','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_35790,c_36806])).

tff(c_36817,plain,(
    m1_connsp_2('#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35785,c_36813])).

tff(c_36819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36215,c_36817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.87/10.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.87/10.01  
% 17.87/10.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.87/10.01  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1 > #skF_6
% 17.87/10.01  
% 17.87/10.01  %Foreground sorts:
% 17.87/10.01  
% 17.87/10.01  
% 17.87/10.01  %Background operators:
% 17.87/10.01  
% 17.87/10.01  
% 17.87/10.01  %Foreground operators:
% 17.87/10.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 17.87/10.01  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 17.87/10.01  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 17.87/10.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.87/10.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.87/10.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.87/10.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.87/10.01  tff('#skF_5', type, '#skF_5': $i).
% 17.87/10.01  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 17.87/10.01  tff('#skF_3', type, '#skF_3': $i).
% 17.87/10.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.87/10.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.87/10.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.87/10.01  tff('#skF_4', type, '#skF_4': $i).
% 17.87/10.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.87/10.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 17.87/10.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.87/10.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.87/10.01  tff('#skF_6', type, '#skF_6': $i > $i).
% 17.87/10.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.87/10.01  
% 17.96/10.04  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.96/10.04  tff(f_167, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 17.96/10.04  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 17.96/10.04  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 17.96/10.04  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 17.96/10.04  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 17.96/10.04  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 17.96/10.04  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 17.96/10.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.96/10.04  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 17.96/10.04  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.96/10.04  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_79, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 17.96/10.04  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_113, plain, (![A_95, B_96]: (r1_tarski(k1_tops_1(A_95, B_96), B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.96/10.04  tff(c_115, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_113])).
% 17.96/10.04  tff(c_118, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_115])).
% 17.96/10.04  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.96/10.04  tff(c_121, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_118, c_8])).
% 17.96/10.04  tff(c_122, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_121])).
% 17.96/10.04  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(k1_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.96/10.04  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_156, plain, (![A_108, B_109]: (k1_tops_1(A_108, k1_tops_1(A_108, B_109))=k1_tops_1(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.96/10.04  tff(c_160, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_156])).
% 17.96/10.04  tff(c_164, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_160])).
% 17.96/10.04  tff(c_710, plain, (![C_176, A_177, B_178]: (m1_connsp_2(C_176, A_177, B_178) | ~r2_hidden(B_178, k1_tops_1(A_177, C_176)) | ~m1_subset_1(C_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~m1_subset_1(B_178, u1_struct_0(A_177)) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.96/10.04  tff(c_731, plain, (![B_178]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_4'), '#skF_3', B_178) | ~r2_hidden(B_178, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_178, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_710])).
% 17.96/10.04  tff(c_750, plain, (![B_178]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_4'), '#skF_3', B_178) | ~r2_hidden(B_178, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_178, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_731])).
% 17.96/10.04  tff(c_751, plain, (![B_178]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_4'), '#skF_3', B_178) | ~r2_hidden(B_178, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_178, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_750])).
% 17.96/10.04  tff(c_778, plain, (~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_751])).
% 17.96/10.04  tff(c_781, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_778])).
% 17.96/10.04  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_781])).
% 17.96/10.04  tff(c_787, plain, (m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_751])).
% 17.96/10.04  tff(c_16, plain, (![A_8, B_9, C_13]: (r2_hidden('#skF_2'(A_8, B_9, C_13), B_9) | r1_tarski(B_9, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.96/10.04  tff(c_18, plain, (![A_8, B_9, C_13]: (m1_subset_1('#skF_2'(A_8, B_9, C_13), A_8) | r1_tarski(B_9, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.96/10.04  tff(c_76, plain, (![C_79]: (v3_pre_topc('#skF_4', '#skF_3') | m1_subset_1('#skF_6'(C_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_194, plain, (![C_79]: (m1_subset_1('#skF_6'(C_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_79, c_76])).
% 17.96/10.04  tff(c_68, plain, (![C_79]: (v3_pre_topc('#skF_4', '#skF_3') | m1_connsp_2('#skF_6'(C_79), '#skF_3', C_79) | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_154, plain, (![C_79]: (m1_connsp_2('#skF_6'(C_79), '#skF_3', C_79) | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_79, c_68])).
% 17.96/10.04  tff(c_60, plain, (![C_79]: (v3_pre_topc('#skF_4', '#skF_3') | r1_tarski('#skF_6'(C_79), '#skF_4') | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_87, plain, (![C_79]: (r1_tarski('#skF_6'(C_79), '#skF_4') | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_79, c_60])).
% 17.96/10.04  tff(c_26, plain, (![A_22, B_26, C_28]: (r1_tarski(k1_tops_1(A_22, B_26), k1_tops_1(A_22, C_28)) | ~r1_tarski(B_26, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.96/10.04  tff(c_311, plain, (![A_132, B_133, C_134]: (r1_tarski(k1_tops_1(A_132, B_133), k1_tops_1(A_132, C_134)) | ~r1_tarski(B_133, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_132))) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.96/10.04  tff(c_330, plain, (![C_134]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k1_tops_1('#skF_3', C_134)) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_311])).
% 17.96/10.04  tff(c_345, plain, (![C_134]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k1_tops_1('#skF_3', C_134)) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_330])).
% 17.96/10.04  tff(c_1884, plain, (![C_261]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k1_tops_1('#skF_3', C_261)) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_345])).
% 17.96/10.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.96/10.04  tff(c_100, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.96/10.04  tff(c_104, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_100])).
% 17.96/10.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.96/10.04  tff(c_111, plain, (![A_92, B_93, B_2, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_2) | ~r1_tarski(B_94, B_2) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_104, c_2])).
% 17.96/10.04  tff(c_2519, plain, (![A_313, B_314, C_315]: (r2_hidden('#skF_1'(A_313, B_314), k1_tops_1('#skF_3', C_315)) | ~r1_tarski(A_313, k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(A_313, B_314) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), C_315) | ~m1_subset_1(C_315, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_1884, c_111])).
% 17.96/10.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.96/10.04  tff(c_2557, plain, (![A_316, C_317]: (~r1_tarski(A_316, k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(A_316, k1_tops_1('#skF_3', C_317)) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_2519, c_4])).
% 17.96/10.04  tff(c_2571, plain, (![B_26, C_317]: (r1_tarski(k1_tops_1('#skF_3', B_26), k1_tops_1('#skF_3', C_317)) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(B_26, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_2557])).
% 17.96/10.04  tff(c_3218, plain, (![B_360, C_361]: (r1_tarski(k1_tops_1('#skF_3', B_360), k1_tops_1('#skF_3', C_361)) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), C_361) | ~m1_subset_1(C_361, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(B_360, '#skF_4') | ~m1_subset_1(B_360, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2571])).
% 17.96/10.04  tff(c_3323, plain, (![B_360]: (r1_tarski(k1_tops_1('#skF_3', B_360), k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(B_360, '#skF_4') | ~m1_subset_1(B_360, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_164, c_3218])).
% 17.96/10.04  tff(c_3380, plain, (![B_362]: (r1_tarski(k1_tops_1('#skF_3', B_362), k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski(B_362, '#skF_4') | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_12, c_3323])).
% 17.96/10.04  tff(c_3695, plain, (![A_375, B_376, B_377]: (r2_hidden('#skF_1'(A_375, B_376), k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski(A_375, k1_tops_1('#skF_3', B_377)) | r1_tarski(A_375, B_376) | ~r1_tarski(B_377, '#skF_4') | ~m1_subset_1(B_377, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_3380, c_111])).
% 17.96/10.04  tff(c_3720, plain, (![B_26, B_376, C_28]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', B_26), B_376), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', B_26), B_376) | ~r1_tarski(C_28, '#skF_4') | ~r1_tarski(B_26, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_3695])).
% 17.96/10.04  tff(c_33502, plain, (![B_1089, B_1090, C_1091]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', B_1089), B_1090), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', B_1089), B_1090) | ~r1_tarski(C_1091, '#skF_4') | ~r1_tarski(B_1089, C_1091) | ~m1_subset_1(C_1091, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_1089, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3720])).
% 17.96/10.04  tff(c_33592, plain, (![C_79, B_1090]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_6'(C_79)), B_1090), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', '#skF_6'(C_79)), B_1090) | ~r1_tarski('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6'(C_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_87, c_33502])).
% 17.96/10.04  tff(c_33673, plain, (![C_1092, B_1093]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_6'(C_1092)), B_1093), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', '#skF_6'(C_1092)), B_1093) | ~m1_subset_1('#skF_6'(C_1092), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_1092, '#skF_4') | ~m1_subset_1(C_1092, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12, c_33592])).
% 17.96/10.04  tff(c_33698, plain, (![C_1094]: (r1_tarski(k1_tops_1('#skF_3', '#skF_6'(C_1094)), k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6'(C_1094), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_1094, '#skF_4') | ~m1_subset_1(C_1094, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_33673, c_4])).
% 17.96/10.04  tff(c_843, plain, (![B_187, A_188, C_189]: (r2_hidden(B_187, k1_tops_1(A_188, C_189)) | ~m1_connsp_2(C_189, A_188, B_187) | ~m1_subset_1(C_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(B_187, u1_struct_0(A_188)) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.96/10.04  tff(c_850, plain, (![B_187, C_79]: (r2_hidden(B_187, k1_tops_1('#skF_3', '#skF_6'(C_79))) | ~m1_connsp_2('#skF_6'(C_79), '#skF_3', B_187) | ~m1_subset_1(B_187, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_194, c_843])).
% 17.96/10.04  tff(c_862, plain, (![B_187, C_79]: (r2_hidden(B_187, k1_tops_1('#skF_3', '#skF_6'(C_79))) | ~m1_connsp_2('#skF_6'(C_79), '#skF_3', B_187) | ~m1_subset_1(B_187, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(C_79, '#skF_4') | ~m1_subset_1(C_79, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_850])).
% 17.96/10.04  tff(c_908, plain, (![B_194, C_195]: (r2_hidden(B_194, k1_tops_1('#skF_3', '#skF_6'(C_195))) | ~m1_connsp_2('#skF_6'(C_195), '#skF_3', B_194) | ~m1_subset_1(B_194, u1_struct_0('#skF_3')) | ~r2_hidden(C_195, '#skF_4') | ~m1_subset_1(C_195, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_862])).
% 17.96/10.04  tff(c_926, plain, (![B_194, B_2, C_195]: (r2_hidden(B_194, B_2) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_6'(C_195)), B_2) | ~m1_connsp_2('#skF_6'(C_195), '#skF_3', B_194) | ~m1_subset_1(B_194, u1_struct_0('#skF_3')) | ~r2_hidden(C_195, '#skF_4') | ~m1_subset_1(C_195, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_908, c_2])).
% 17.96/10.04  tff(c_34083, plain, (![B_1101, C_1102]: (r2_hidden(B_1101, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_6'(C_1102), '#skF_3', B_1101) | ~m1_subset_1(B_1101, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6'(C_1102), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_1102, '#skF_4') | ~m1_subset_1(C_1102, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_33698, c_926])).
% 17.96/10.04  tff(c_34104, plain, (![C_1103]: (r2_hidden(C_1103, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6'(C_1103), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_1103, '#skF_4') | ~m1_subset_1(C_1103, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_154, c_34083])).
% 17.96/10.04  tff(c_34109, plain, (![C_1104]: (r2_hidden(C_1104, k1_tops_1('#skF_3', '#skF_4')) | ~r2_hidden(C_1104, '#skF_4') | ~m1_subset_1(C_1104, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_194, c_34104])).
% 17.96/10.04  tff(c_32, plain, (![C_50, A_44, B_48]: (m1_connsp_2(C_50, A_44, B_48) | ~r2_hidden(B_48, k1_tops_1(A_44, C_50)) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_48, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.96/10.04  tff(c_34121, plain, (![C_1104]: (m1_connsp_2('#skF_4', '#skF_3', C_1104) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_1104, '#skF_4') | ~m1_subset_1(C_1104, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_34109, c_32])).
% 17.96/10.04  tff(c_34138, plain, (![C_1104]: (m1_connsp_2('#skF_4', '#skF_3', C_1104) | v2_struct_0('#skF_3') | ~r2_hidden(C_1104, '#skF_4') | ~m1_subset_1(C_1104, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_34121])).
% 17.96/10.04  tff(c_34143, plain, (![C_1105]: (m1_connsp_2('#skF_4', '#skF_3', C_1105) | ~r2_hidden(C_1105, '#skF_4') | ~m1_subset_1(C_1105, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_34138])).
% 17.96/10.04  tff(c_35283, plain, (![B_1139, C_1140]: (m1_connsp_2('#skF_4', '#skF_3', '#skF_2'(u1_struct_0('#skF_3'), B_1139, C_1140)) | ~r2_hidden('#skF_2'(u1_struct_0('#skF_3'), B_1139, C_1140), '#skF_4') | r1_tarski(B_1139, C_1140) | ~m1_subset_1(C_1140, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_1139, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_18, c_34143])).
% 17.96/10.04  tff(c_854, plain, (![B_187]: (r2_hidden(B_187, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_187) | ~m1_subset_1(B_187, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_843])).
% 17.96/10.04  tff(c_867, plain, (![B_187]: (r2_hidden(B_187, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_187) | ~m1_subset_1(B_187, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_854])).
% 17.96/10.04  tff(c_869, plain, (![B_190]: (r2_hidden(B_190, k1_tops_1('#skF_3', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_3', B_190) | ~m1_subset_1(B_190, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_867])).
% 17.96/10.04  tff(c_14, plain, (![A_8, B_9, C_13]: (~r2_hidden('#skF_2'(A_8, B_9, C_13), C_13) | r1_tarski(B_9, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.96/10.04  tff(c_6188, plain, (![B_484, A_485]: (r1_tarski(B_484, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(A_485)) | ~m1_subset_1(B_484, k1_zfmisc_1(A_485)) | ~m1_connsp_2('#skF_4', '#skF_3', '#skF_2'(A_485, B_484, k1_tops_1('#skF_3', '#skF_4'))) | ~m1_subset_1('#skF_2'(A_485, B_484, k1_tops_1('#skF_3', '#skF_4')), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_869, c_14])).
% 17.96/10.04  tff(c_6192, plain, (![B_9]: (~m1_connsp_2('#skF_4', '#skF_3', '#skF_2'(u1_struct_0('#skF_3'), B_9, k1_tops_1('#skF_3', '#skF_4'))) | r1_tarski(B_9, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_18, c_6188])).
% 17.96/10.04  tff(c_6195, plain, (![B_9]: (~m1_connsp_2('#skF_4', '#skF_3', '#skF_2'(u1_struct_0('#skF_3'), B_9, k1_tops_1('#skF_3', '#skF_4'))) | r1_tarski(B_9, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_6192])).
% 17.96/10.04  tff(c_35290, plain, (![B_1139]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_3'), B_1139, k1_tops_1('#skF_3', '#skF_4')), '#skF_4') | r1_tarski(B_1139, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_1139, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_35283, c_6195])).
% 17.96/10.04  tff(c_35295, plain, (![B_1141]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_3'), B_1141, k1_tops_1('#skF_3', '#skF_4')), '#skF_4') | r1_tarski(B_1141, k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(B_1141, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_35290])).
% 17.96/10.04  tff(c_35331, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_35295])).
% 17.96/10.04  tff(c_35358, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_787, c_35331])).
% 17.96/10.04  tff(c_35360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_35358])).
% 17.96/10.04  tff(c_35361, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_121])).
% 17.96/10.04  tff(c_28, plain, (![C_41, A_29, D_43, B_37]: (v3_pre_topc(C_41, A_29) | k1_tops_1(A_29, C_41)!=C_41 | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0(B_37))) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(B_37) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_104])).
% 17.96/10.04  tff(c_35741, plain, (![D_1194, B_1195]: (~m1_subset_1(D_1194, k1_zfmisc_1(u1_struct_0(B_1195))) | ~l1_pre_topc(B_1195))), inference(splitLeft, [status(thm)], [c_28])).
% 17.96/10.04  tff(c_35751, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_35741])).
% 17.96/10.04  tff(c_35759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_35751])).
% 17.96/10.04  tff(c_35761, plain, (![C_1196, A_1197]: (v3_pre_topc(C_1196, A_1197) | k1_tops_1(A_1197, C_1196)!=C_1196 | ~m1_subset_1(C_1196, k1_zfmisc_1(u1_struct_0(A_1197))) | ~l1_pre_topc(A_1197) | ~v2_pre_topc(A_1197))), inference(splitRight, [status(thm)], [c_28])).
% 17.96/10.04  tff(c_35774, plain, (v3_pre_topc('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_35761])).
% 17.96/10.04  tff(c_35782, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_35361, c_35774])).
% 17.96/10.04  tff(c_35784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_35782])).
% 17.96/10.04  tff(c_35786, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 17.96/10.04  tff(c_46, plain, (![D_78]: (~r1_tarski(D_78, '#skF_4') | ~m1_connsp_2(D_78, '#skF_3', '#skF_5') | ~m1_subset_1(D_78, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_36202, plain, (![D_1270]: (~r1_tarski(D_1270, '#skF_4') | ~m1_connsp_2(D_1270, '#skF_3', '#skF_5') | ~m1_subset_1(D_1270, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_35786, c_46])).
% 17.96/10.04  tff(c_36209, plain, (~r1_tarski('#skF_4', '#skF_4') | ~m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_36202])).
% 17.96/10.04  tff(c_36215, plain, (~m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36209])).
% 17.96/10.04  tff(c_35785, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 17.96/10.04  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 17.96/10.04  tff(c_35787, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 17.96/10.04  tff(c_35789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35786, c_35787])).
% 17.96/10.04  tff(c_35790, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 17.96/10.04  tff(c_30, plain, (![B_37, D_43, C_41, A_29]: (k1_tops_1(B_37, D_43)=D_43 | ~v3_pre_topc(D_43, B_37) | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0(B_37))) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(B_37) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_104])).
% 17.96/10.04  tff(c_36134, plain, (![C_1262, A_1263]: (~m1_subset_1(C_1262, k1_zfmisc_1(u1_struct_0(A_1263))) | ~l1_pre_topc(A_1263) | ~v2_pre_topc(A_1263))), inference(splitLeft, [status(thm)], [c_30])).
% 17.96/10.04  tff(c_36144, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_36134])).
% 17.96/10.04  tff(c_36150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36144])).
% 17.96/10.04  tff(c_36152, plain, (![B_1264, D_1265]: (k1_tops_1(B_1264, D_1265)=D_1265 | ~v3_pre_topc(D_1265, B_1264) | ~m1_subset_1(D_1265, k1_zfmisc_1(u1_struct_0(B_1264))) | ~l1_pre_topc(B_1264))), inference(splitRight, [status(thm)], [c_30])).
% 17.96/10.04  tff(c_36162, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_36152])).
% 17.96/10.04  tff(c_36167, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_35786, c_36162])).
% 17.96/10.04  tff(c_35833, plain, (![A_1213, B_1214]: (r1_tarski(k1_tops_1(A_1213, B_1214), B_1214) | ~m1_subset_1(B_1214, k1_zfmisc_1(u1_struct_0(A_1213))) | ~l1_pre_topc(A_1213))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.96/10.04  tff(c_35835, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_35833])).
% 17.96/10.04  tff(c_35838, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_35835])).
% 17.96/10.04  tff(c_35845, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_35838, c_8])).
% 17.96/10.04  tff(c_35850, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_35845])).
% 17.96/10.04  tff(c_36175, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36167, c_35850])).
% 17.96/10.04  tff(c_36179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_36175])).
% 17.96/10.04  tff(c_36180, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_35845])).
% 17.96/10.04  tff(c_36772, plain, (![C_1328, A_1329, B_1330]: (m1_connsp_2(C_1328, A_1329, B_1330) | ~r2_hidden(B_1330, k1_tops_1(A_1329, C_1328)) | ~m1_subset_1(C_1328, k1_zfmisc_1(u1_struct_0(A_1329))) | ~m1_subset_1(B_1330, u1_struct_0(A_1329)) | ~l1_pre_topc(A_1329) | ~v2_pre_topc(A_1329) | v2_struct_0(A_1329))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.96/10.04  tff(c_36784, plain, (![B_1330]: (m1_connsp_2('#skF_4', '#skF_3', B_1330) | ~r2_hidden(B_1330, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_1330, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36180, c_36772])).
% 17.96/10.04  tff(c_36801, plain, (![B_1330]: (m1_connsp_2('#skF_4', '#skF_3', B_1330) | ~r2_hidden(B_1330, '#skF_4') | ~m1_subset_1(B_1330, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36784])).
% 17.96/10.04  tff(c_36806, plain, (![B_1331]: (m1_connsp_2('#skF_4', '#skF_3', B_1331) | ~r2_hidden(B_1331, '#skF_4') | ~m1_subset_1(B_1331, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_36801])).
% 17.96/10.04  tff(c_36813, plain, (m1_connsp_2('#skF_4', '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_35790, c_36806])).
% 17.96/10.04  tff(c_36817, plain, (m1_connsp_2('#skF_4', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35785, c_36813])).
% 17.96/10.04  tff(c_36819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36215, c_36817])).
% 17.96/10.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.96/10.04  
% 17.96/10.04  Inference rules
% 17.96/10.04  ----------------------
% 17.96/10.04  #Ref     : 0
% 17.96/10.04  #Sup     : 8436
% 17.96/10.04  #Fact    : 0
% 17.96/10.04  #Define  : 0
% 17.96/10.04  #Split   : 17
% 17.96/10.04  #Chain   : 0
% 17.96/10.04  #Close   : 0
% 17.96/10.04  
% 17.96/10.04  Ordering : KBO
% 17.96/10.04  
% 17.96/10.04  Simplification rules
% 17.96/10.04  ----------------------
% 17.96/10.04  #Subsume      : 4367
% 17.96/10.04  #Demod        : 6414
% 17.96/10.04  #Tautology    : 636
% 17.96/10.04  #SimpNegUnit  : 412
% 17.96/10.04  #BackRed      : 9
% 17.96/10.04  
% 17.96/10.04  #Partial instantiations: 0
% 17.96/10.04  #Strategies tried      : 1
% 17.96/10.04  
% 17.96/10.04  Timing (in seconds)
% 17.96/10.04  ----------------------
% 17.96/10.04  Preprocessing        : 0.32
% 17.96/10.04  Parsing              : 0.17
% 17.96/10.04  CNF conversion       : 0.03
% 17.96/10.04  Main loop            : 8.81
% 17.96/10.04  Inferencing          : 1.35
% 17.96/10.04  Reduction            : 1.73
% 17.96/10.04  Demodulation         : 1.18
% 17.96/10.04  BG Simplification    : 0.13
% 17.96/10.04  Subsumption          : 5.24
% 17.96/10.04  Abstraction          : 0.25
% 17.96/10.04  MUC search           : 0.00
% 17.96/10.04  Cooper               : 0.00
% 17.96/10.04  Total                : 9.18
% 17.96/10.04  Index Insertion      : 0.00
% 17.96/10.04  Index Deletion       : 0.00
% 17.96/10.04  Index Matching       : 0.00
% 17.96/10.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
