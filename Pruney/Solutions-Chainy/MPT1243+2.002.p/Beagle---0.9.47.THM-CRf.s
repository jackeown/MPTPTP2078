%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:49 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 237 expanded)
%              Number of leaves         :   25 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  203 ( 843 expanded)
%              Number of equality atoms :    4 (  13 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> ! [C] :
                  ( r2_hidden(C,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,B)
                      & r2_hidden(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_178,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_24,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_214,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_tops_1(A_78,B_79),B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_218,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_214])).

tff(c_224,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_218])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_227,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_224,c_8])).

tff(c_228,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [C_54] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | r1_tarski('#skF_7'(C_54),'#skF_3')
      | ~ r2_hidden(C_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_187,plain,(
    ! [C_54] :
      ( r1_tarski('#skF_7'(C_54),'#skF_3')
      | ~ r2_hidden(C_54,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_70])).

tff(c_92,plain,(
    ! [C_54] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | v3_pre_topc('#skF_7'(C_54),'#skF_2')
      | ~ r2_hidden(C_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_185,plain,(
    ! [C_54] :
      ( v3_pre_topc('#skF_7'(C_54),'#skF_2')
      | ~ r2_hidden(C_54,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_92])).

tff(c_114,plain,(
    ! [C_54] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | m1_subset_1('#skF_7'(C_54),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_212,plain,(
    ! [C_54] :
      ( m1_subset_1('#skF_7'(C_54),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_54,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_114])).

tff(c_584,plain,(
    ! [B_153,A_154,C_155] :
      ( r1_tarski(B_153,k1_tops_1(A_154,C_155))
      | ~ r1_tarski(B_153,C_155)
      | ~ v3_pre_topc(B_153,A_154)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_588,plain,(
    ! [B_153] :
      ( r1_tarski(B_153,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_153,'#skF_3')
      | ~ v3_pre_topc(B_153,'#skF_2')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_584])).

tff(c_595,plain,(
    ! [B_156] :
      ( r1_tarski(B_156,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_156,'#skF_3')
      | ~ v3_pre_topc(B_156,'#skF_2')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_588])).

tff(c_607,plain,(
    ! [C_157] :
      ( r1_tarski('#skF_7'(C_157),k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'(C_157),'#skF_3')
      | ~ v3_pre_topc('#skF_7'(C_157),'#skF_2')
      | ~ r2_hidden(C_157,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_212,c_595])).

tff(c_48,plain,(
    ! [C_54] :
      ( v3_pre_topc('#skF_3','#skF_2')
      | r2_hidden(C_54,'#skF_7'(C_54))
      | ~ r2_hidden(C_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_181,plain,(
    ! [C_68] :
      ( r2_hidden(C_68,'#skF_7'(C_68))
      | ~ r2_hidden(C_68,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_48])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_184,plain,(
    ! [C_68,B_2] :
      ( r2_hidden(C_68,B_2)
      | ~ r1_tarski('#skF_7'(C_68),B_2)
      | ~ r2_hidden(C_68,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_181,c_2])).

tff(c_628,plain,(
    ! [C_158] :
      ( r2_hidden(C_158,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'(C_158),'#skF_3')
      | ~ v3_pre_topc('#skF_7'(C_158),'#skF_2')
      | ~ r2_hidden(C_158,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_607,c_184])).

tff(c_633,plain,(
    ! [C_159] :
      ( r2_hidden(C_159,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'(C_159),'#skF_3')
      | ~ r2_hidden(C_159,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_185,c_628])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_650,plain,(
    ! [A_162] :
      ( r1_tarski(A_162,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski('#skF_7'('#skF_1'(A_162,k1_tops_1('#skF_2','#skF_3'))),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_162,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_633,c_4])).

tff(c_661,plain,(
    ! [A_163] :
      ( r1_tarski(A_163,k1_tops_1('#skF_2','#skF_3'))
      | ~ r2_hidden('#skF_1'(A_163,k1_tops_1('#skF_2','#skF_3')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_187,c_650])).

tff(c_693,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_661])).

tff(c_710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_228,c_693])).

tff(c_711,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_724,plain,(
    ! [A_165,B_166] :
      ( v3_pre_topc(k1_tops_1(A_165,B_166),A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_728,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_724])).

tff(c_734,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_711,c_728])).

tff(c_736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_734])).

tff(c_738,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_741,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_40])).

tff(c_742,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_32,plain,(
    ! [D_53] :
      ( r1_tarski('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_6',D_53)
      | ~ r1_tarski(D_53,'#skF_3')
      | ~ v3_pre_topc(D_53,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_858,plain,(
    ! [D_53] :
      ( r1_tarski('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_6',D_53)
      | ~ r1_tarski(D_53,'#skF_3')
      | ~ v3_pre_topc(D_53,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_32])).

tff(c_862,plain,(
    ! [D_193] :
      ( ~ r2_hidden('#skF_6',D_193)
      | ~ r1_tarski(D_193,'#skF_3')
      | ~ v3_pre_topc(D_193,'#skF_2')
      | ~ m1_subset_1(D_193,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_858])).

tff(c_865,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_862])).

tff(c_869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_12,c_742,c_865])).

tff(c_870,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_858])).

tff(c_30,plain,(
    ! [D_53] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r2_hidden('#skF_6',D_53)
      | ~ r1_tarski(D_53,'#skF_3')
      | ~ v3_pre_topc(D_53,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_940,plain,(
    ! [D_53] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r2_hidden('#skF_6',D_53)
      | ~ r1_tarski(D_53,'#skF_3')
      | ~ v3_pre_topc(D_53,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_30])).

tff(c_942,plain,(
    ! [D_207] :
      ( ~ r2_hidden('#skF_6',D_207)
      | ~ r1_tarski(D_207,'#skF_3')
      | ~ v3_pre_topc(D_207,'#skF_2')
      | ~ m1_subset_1(D_207,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_945,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_942])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_12,c_742,c_945])).

tff(c_950,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_954,plain,(
    ! [B_208] :
      ( r2_hidden('#skF_4',B_208)
      | ~ r1_tarski('#skF_5',B_208) ) ),
    inference(resolution,[status(thm)],[c_950,c_2])).

tff(c_737,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_739,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_737])).

tff(c_957,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_954,c_739])).

tff(c_963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_957])).

tff(c_965,plain,(
    ~ r2_hidden('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_42,plain,
    ( r1_tarski('#skF_5','#skF_3')
    | r2_hidden('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_970,plain,
    ( r1_tarski('#skF_5','#skF_3')
    | r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_42])).

tff(c_971,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_965,c_970])).

tff(c_964,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_976,plain,(
    ! [B_209] :
      ( r2_hidden('#skF_4',B_209)
      | ~ r1_tarski('#skF_5',B_209) ) ),
    inference(resolution,[status(thm)],[c_964,c_2])).

tff(c_979,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_976,c_739])).

tff(c_985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_979])).

tff(c_986,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_737])).

tff(c_987,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_737])).

tff(c_28,plain,(
    ! [D_53] :
      ( ~ r2_hidden('#skF_4','#skF_3')
      | ~ r2_hidden('#skF_6',D_53)
      | ~ r1_tarski(D_53,'#skF_3')
      | ~ v3_pre_topc(D_53,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc('#skF_3','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1152,plain,(
    ! [D_243] :
      ( ~ r2_hidden('#skF_6',D_243)
      | ~ r1_tarski(D_243,'#skF_3')
      | ~ v3_pre_topc(D_243,'#skF_2')
      | ~ m1_subset_1(D_243,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_987,c_28])).

tff(c_1155,plain,
    ( ~ r2_hidden('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1152])).

tff(c_1159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_12,c_986,c_1155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.66  
% 4.15/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.67  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.15/1.67  
% 4.15/1.67  %Foreground sorts:
% 4.15/1.67  
% 4.15/1.67  
% 4.15/1.67  %Background operators:
% 4.15/1.67  
% 4.15/1.67  
% 4.15/1.67  %Foreground operators:
% 4.15/1.67  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.15/1.67  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.15/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.15/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.67  tff('#skF_5', type, '#skF_5': $i).
% 4.15/1.67  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.15/1.67  tff('#skF_6', type, '#skF_6': $i).
% 4.15/1.67  tff('#skF_2', type, '#skF_2': $i).
% 4.15/1.67  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.67  tff('#skF_4', type, '#skF_4': $i).
% 4.15/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.15/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.15/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.15/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.67  
% 4.38/1.68  tff(f_89, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, B)) & r2_hidden(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tops_1)).
% 4.38/1.68  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.38/1.68  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.38/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.38/1.68  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.38/1.68  tff(f_46, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.38/1.68  tff(c_38, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_178, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 4.38/1.68  tff(c_24, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_214, plain, (![A_78, B_79]: (r1_tarski(k1_tops_1(A_78, B_79), B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.38/1.68  tff(c_218, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_214])).
% 4.38/1.68  tff(c_224, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_218])).
% 4.38/1.68  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.38/1.68  tff(c_227, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_224, c_8])).
% 4.38/1.68  tff(c_228, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_227])).
% 4.38/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.38/1.68  tff(c_70, plain, (![C_54]: (v3_pre_topc('#skF_3', '#skF_2') | r1_tarski('#skF_7'(C_54), '#skF_3') | ~r2_hidden(C_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_187, plain, (![C_54]: (r1_tarski('#skF_7'(C_54), '#skF_3') | ~r2_hidden(C_54, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_178, c_70])).
% 4.38/1.68  tff(c_92, plain, (![C_54]: (v3_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_7'(C_54), '#skF_2') | ~r2_hidden(C_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_185, plain, (![C_54]: (v3_pre_topc('#skF_7'(C_54), '#skF_2') | ~r2_hidden(C_54, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_178, c_92])).
% 4.38/1.68  tff(c_114, plain, (![C_54]: (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1('#skF_7'(C_54), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_212, plain, (![C_54]: (m1_subset_1('#skF_7'(C_54), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_54, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_178, c_114])).
% 4.38/1.68  tff(c_584, plain, (![B_153, A_154, C_155]: (r1_tarski(B_153, k1_tops_1(A_154, C_155)) | ~r1_tarski(B_153, C_155) | ~v3_pre_topc(B_153, A_154) | ~m1_subset_1(C_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.38/1.68  tff(c_588, plain, (![B_153]: (r1_tarski(B_153, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_153, '#skF_3') | ~v3_pre_topc(B_153, '#skF_2') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_584])).
% 4.38/1.68  tff(c_595, plain, (![B_156]: (r1_tarski(B_156, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_156, '#skF_3') | ~v3_pre_topc(B_156, '#skF_2') | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_588])).
% 4.38/1.68  tff(c_607, plain, (![C_157]: (r1_tarski('#skF_7'(C_157), k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'(C_157), '#skF_3') | ~v3_pre_topc('#skF_7'(C_157), '#skF_2') | ~r2_hidden(C_157, '#skF_3'))), inference(resolution, [status(thm)], [c_212, c_595])).
% 4.38/1.68  tff(c_48, plain, (![C_54]: (v3_pre_topc('#skF_3', '#skF_2') | r2_hidden(C_54, '#skF_7'(C_54)) | ~r2_hidden(C_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_181, plain, (![C_68]: (r2_hidden(C_68, '#skF_7'(C_68)) | ~r2_hidden(C_68, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_178, c_48])).
% 4.38/1.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.38/1.68  tff(c_184, plain, (![C_68, B_2]: (r2_hidden(C_68, B_2) | ~r1_tarski('#skF_7'(C_68), B_2) | ~r2_hidden(C_68, '#skF_3'))), inference(resolution, [status(thm)], [c_181, c_2])).
% 4.38/1.68  tff(c_628, plain, (![C_158]: (r2_hidden(C_158, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'(C_158), '#skF_3') | ~v3_pre_topc('#skF_7'(C_158), '#skF_2') | ~r2_hidden(C_158, '#skF_3'))), inference(resolution, [status(thm)], [c_607, c_184])).
% 4.38/1.68  tff(c_633, plain, (![C_159]: (r2_hidden(C_159, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'(C_159), '#skF_3') | ~r2_hidden(C_159, '#skF_3'))), inference(resolution, [status(thm)], [c_185, c_628])).
% 4.38/1.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.38/1.68  tff(c_650, plain, (![A_162]: (r1_tarski(A_162, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_7'('#skF_1'(A_162, k1_tops_1('#skF_2', '#skF_3'))), '#skF_3') | ~r2_hidden('#skF_1'(A_162, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_633, c_4])).
% 4.38/1.68  tff(c_661, plain, (![A_163]: (r1_tarski(A_163, k1_tops_1('#skF_2', '#skF_3')) | ~r2_hidden('#skF_1'(A_163, k1_tops_1('#skF_2', '#skF_3')), '#skF_3'))), inference(resolution, [status(thm)], [c_187, c_650])).
% 4.38/1.68  tff(c_693, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_661])).
% 4.38/1.68  tff(c_710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_228, c_693])).
% 4.38/1.68  tff(c_711, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_227])).
% 4.38/1.68  tff(c_724, plain, (![A_165, B_166]: (v3_pre_topc(k1_tops_1(A_165, B_166), A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.38/1.68  tff(c_728, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_724])).
% 4.38/1.68  tff(c_734, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_711, c_728])).
% 4.38/1.68  tff(c_736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_734])).
% 4.38/1.68  tff(c_738, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 4.38/1.68  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.38/1.68  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_741, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_40])).
% 4.38/1.68  tff(c_742, plain, (r2_hidden('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_741])).
% 4.38/1.68  tff(c_32, plain, (![D_53]: (r1_tarski('#skF_5', '#skF_3') | ~r2_hidden('#skF_6', D_53) | ~r1_tarski(D_53, '#skF_3') | ~v3_pre_topc(D_53, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_858, plain, (![D_53]: (r1_tarski('#skF_5', '#skF_3') | ~r2_hidden('#skF_6', D_53) | ~r1_tarski(D_53, '#skF_3') | ~v3_pre_topc(D_53, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_32])).
% 4.38/1.68  tff(c_862, plain, (![D_193]: (~r2_hidden('#skF_6', D_193) | ~r1_tarski(D_193, '#skF_3') | ~v3_pre_topc(D_193, '#skF_2') | ~m1_subset_1(D_193, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_858])).
% 4.38/1.68  tff(c_865, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_862])).
% 4.38/1.68  tff(c_869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_12, c_742, c_865])).
% 4.38/1.68  tff(c_870, plain, (r1_tarski('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_858])).
% 4.38/1.68  tff(c_30, plain, (![D_53]: (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_6', D_53) | ~r1_tarski(D_53, '#skF_3') | ~v3_pre_topc(D_53, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_940, plain, (![D_53]: (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_6', D_53) | ~r1_tarski(D_53, '#skF_3') | ~v3_pre_topc(D_53, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_30])).
% 4.38/1.68  tff(c_942, plain, (![D_207]: (~r2_hidden('#skF_6', D_207) | ~r1_tarski(D_207, '#skF_3') | ~v3_pre_topc(D_207, '#skF_2') | ~m1_subset_1(D_207, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_940])).
% 4.38/1.68  tff(c_945, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_942])).
% 4.38/1.68  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_12, c_742, c_945])).
% 4.38/1.68  tff(c_950, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_940])).
% 4.38/1.68  tff(c_954, plain, (![B_208]: (r2_hidden('#skF_4', B_208) | ~r1_tarski('#skF_5', B_208))), inference(resolution, [status(thm)], [c_950, c_2])).
% 4.38/1.68  tff(c_737, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 4.38/1.68  tff(c_739, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_737])).
% 4.38/1.68  tff(c_957, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_954, c_739])).
% 4.38/1.68  tff(c_963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_870, c_957])).
% 4.38/1.68  tff(c_965, plain, (~r2_hidden('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_741])).
% 4.38/1.68  tff(c_42, plain, (r1_tarski('#skF_5', '#skF_3') | r2_hidden('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_970, plain, (r1_tarski('#skF_5', '#skF_3') | r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_42])).
% 4.38/1.68  tff(c_971, plain, (r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_965, c_970])).
% 4.38/1.68  tff(c_964, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_741])).
% 4.38/1.68  tff(c_976, plain, (![B_209]: (r2_hidden('#skF_4', B_209) | ~r1_tarski('#skF_5', B_209))), inference(resolution, [status(thm)], [c_964, c_2])).
% 4.38/1.68  tff(c_979, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_976, c_739])).
% 4.38/1.68  tff(c_985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_971, c_979])).
% 4.38/1.68  tff(c_986, plain, (r2_hidden('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_737])).
% 4.38/1.68  tff(c_987, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_737])).
% 4.38/1.68  tff(c_28, plain, (![D_53]: (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_6', D_53) | ~r1_tarski(D_53, '#skF_3') | ~v3_pre_topc(D_53, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.38/1.68  tff(c_1152, plain, (![D_243]: (~r2_hidden('#skF_6', D_243) | ~r1_tarski(D_243, '#skF_3') | ~v3_pre_topc(D_243, '#skF_2') | ~m1_subset_1(D_243, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_987, c_28])).
% 4.38/1.68  tff(c_1155, plain, (~r2_hidden('#skF_6', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_1152])).
% 4.38/1.68  tff(c_1159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_12, c_986, c_1155])).
% 4.38/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.68  
% 4.38/1.68  Inference rules
% 4.38/1.68  ----------------------
% 4.38/1.68  #Ref     : 0
% 4.38/1.68  #Sup     : 199
% 4.38/1.68  #Fact    : 0
% 4.38/1.68  #Define  : 0
% 4.38/1.68  #Split   : 13
% 4.38/1.68  #Chain   : 0
% 4.38/1.68  #Close   : 0
% 4.38/1.68  
% 4.38/1.68  Ordering : KBO
% 4.38/1.68  
% 4.38/1.68  Simplification rules
% 4.38/1.68  ----------------------
% 4.38/1.68  #Subsume      : 120
% 4.38/1.68  #Demod        : 133
% 4.38/1.69  #Tautology    : 76
% 4.38/1.69  #SimpNegUnit  : 8
% 4.38/1.69  #BackRed      : 1
% 4.38/1.69  
% 4.38/1.69  #Partial instantiations: 0
% 4.38/1.69  #Strategies tried      : 1
% 4.38/1.69  
% 4.38/1.69  Timing (in seconds)
% 4.38/1.69  ----------------------
% 4.38/1.69  Preprocessing        : 0.35
% 4.38/1.69  Parsing              : 0.16
% 4.38/1.69  CNF conversion       : 0.03
% 4.38/1.69  Main loop            : 0.57
% 4.38/1.69  Inferencing          : 0.16
% 4.38/1.69  Reduction            : 0.15
% 4.38/1.69  Demodulation         : 0.09
% 4.38/1.69  BG Simplification    : 0.03
% 4.38/1.69  Subsumption          : 0.19
% 4.38/1.69  Abstraction          : 0.02
% 4.38/1.69  MUC search           : 0.00
% 4.38/1.69  Cooper               : 0.00
% 4.38/1.69  Total                : 0.96
% 4.38/1.69  Index Insertion      : 0.00
% 4.38/1.69  Index Deletion       : 0.00
% 4.38/1.69  Index Matching       : 0.00
% 4.38/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
