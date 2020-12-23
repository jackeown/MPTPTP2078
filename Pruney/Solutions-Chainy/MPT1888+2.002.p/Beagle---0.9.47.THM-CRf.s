%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:20 EST 2020

% Result     : Theorem 13.48s
% Output     : CNFRefutation 13.48s
% Verified   : 
% Statistics : Number of formulae       :  125 (1051 expanded)
%              Number of leaves         :   35 ( 366 expanded)
%              Depth                    :   17
%              Number of atoms          :  275 (3450 expanded)
%              Number of equality atoms :   30 ( 641 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
                  | k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
               => k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_162,plain,(
    ! [B_74,A_75] :
      ( r2_hidden(B_74,k1_connsp_2(A_75,B_74))
      | ~ m1_subset_1(B_74,u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_278,plain,(
    ! [A_93,B_94] :
      ( ~ v1_xboole_0(k1_connsp_2(A_93,B_94))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_293,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_3','#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_278])).

tff(c_302,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_3','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_293])).

tff(c_303,plain,(
    ~ v1_xboole_0(k1_connsp_2('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_302])).

tff(c_104,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_115,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_104])).

tff(c_117,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_237,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1(k1_connsp_2(A_89,B_90),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( v1_xboole_0(B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_472,plain,(
    ! [A_120,B_121] :
      ( v1_xboole_0(k1_connsp_2(A_120,B_121))
      | ~ v1_xboole_0(u1_struct_0(A_120))
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_237,c_16])).

tff(c_487,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_3','#skF_5'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_472])).

tff(c_496,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_3','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_117,c_487])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_303,c_496])).

tff(c_500,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_116,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_104])).

tff(c_508,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_116])).

tff(c_499,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_502,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_34])).

tff(c_544,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_502])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k1_tarski(A_11),k1_zfmisc_1(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_2'(A_51,B_52),B_52)
      | r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [B_52,A_51] :
      ( ~ v1_xboole_0(B_52)
      | r1_xboole_0(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_102,plain,(
    ~ v1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ),
    inference(resolution,[status(thm)],[c_73,c_34])).

tff(c_501,plain,(
    ~ v1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_102])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_514,plain,(
    ! [A_122,B_123] :
      ( m1_subset_1(k2_pre_topc(A_122,B_123),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_18,C_20,B_19] :
      ( m1_subset_1(A_18,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_793,plain,(
    ! [A_164,A_165,B_166] :
      ( m1_subset_1(A_164,u1_struct_0(A_165))
      | ~ r2_hidden(A_164,k2_pre_topc(A_165,B_166))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(resolution,[status(thm)],[c_514,c_20])).

tff(c_809,plain,(
    ! [A_165,B_166] :
      ( m1_subset_1('#skF_1'(k2_pre_topc(A_165,B_166)),u1_struct_0(A_165))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165)
      | v1_xboole_0(k2_pre_topc(A_165,B_166)) ) ),
    inference(resolution,[status(thm)],[c_4,c_793])).

tff(c_42,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_833,plain,(
    ! [A_169,C_170,B_171] :
      ( k2_pre_topc(A_169,k6_domain_1(u1_struct_0(A_169),C_170)) = k2_pre_topc(A_169,k6_domain_1(u1_struct_0(A_169),B_171))
      | ~ r2_hidden(B_171,k2_pre_topc(A_169,k6_domain_1(u1_struct_0(A_169),C_170)))
      | ~ m1_subset_1(C_170,u1_struct_0(A_169))
      | ~ m1_subset_1(B_171,u1_struct_0(A_169))
      | ~ l1_pre_topc(A_169)
      | ~ v3_tdlat_3(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1836,plain,(
    ! [A_269,C_270] :
      ( k2_pre_topc(A_269,k6_domain_1(u1_struct_0(A_269),'#skF_1'(k2_pre_topc(A_269,k6_domain_1(u1_struct_0(A_269),C_270))))) = k2_pre_topc(A_269,k6_domain_1(u1_struct_0(A_269),C_270))
      | ~ m1_subset_1(C_270,u1_struct_0(A_269))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc(A_269,k6_domain_1(u1_struct_0(A_269),C_270))),u1_struct_0(A_269))
      | ~ l1_pre_topc(A_269)
      | ~ v3_tdlat_3(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269)
      | v1_xboole_0(k2_pre_topc(A_269,k6_domain_1(u1_struct_0(A_269),C_270))) ) ),
    inference(resolution,[status(thm)],[c_4,c_833])).

tff(c_1895,plain,
    ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))) = k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_1836])).

tff(c_1907,plain,
    ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))) = k2_pre_topc('#skF_3',k1_tarski('#skF_5'))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_44,c_42,c_40,c_499,c_36,c_499,c_1895])).

tff(c_1908,plain,
    ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))) = k2_pre_topc('#skF_3',k1_tarski('#skF_5'))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_46,c_1907])).

tff(c_2169,plain,(
    ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1908])).

tff(c_2172,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | v1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_809,c_2169])).

tff(c_2175,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2172])).

tff(c_2176,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_2175])).

tff(c_2180,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_2176])).

tff(c_2183,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_2180])).

tff(c_2186,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2183])).

tff(c_2188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_2186])).

tff(c_2190,plain,(
    m1_subset_1('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1908])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( k6_domain_1(A_23,B_24) = k1_tarski(B_24)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2201,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5')))) = k1_tarski('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2190,c_24])).

tff(c_2215,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5')))) = k1_tarski('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_2201])).

tff(c_2189,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))) = k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1908])).

tff(c_2400,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))) = k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2215,c_2189])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_pre_topc(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2455,plain,
    ( m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k1_tarski('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5')))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2400,c_22])).

tff(c_2472,plain,
    ( m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k1_tarski('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5')))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2455])).

tff(c_3599,plain,(
    ~ m1_subset_1(k1_tarski('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5')))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2472])).

tff(c_3603,plain,(
    ~ r2_hidden('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_3599])).

tff(c_3606,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_3603])).

tff(c_3609,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_3606])).

tff(c_3611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_3609])).

tff(c_3612,plain,(
    m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2472])).

tff(c_3818,plain,(
    ! [A_336] :
      ( m1_subset_1(A_336,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_336,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_3612,c_20])).

tff(c_3838,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3'))
      | r1_xboole_0(A_5,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_3818])).

tff(c_32,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_503,plain,(
    k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')) != k2_pre_topc('#skF_3',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_32])).

tff(c_526,plain,(
    k2_pre_topc('#skF_3',k1_tarski('#skF_5')) != k2_pre_topc('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_503])).

tff(c_1957,plain,(
    ! [A_271,A_272,C_273] :
      ( k2_pre_topc(A_271,k6_domain_1(u1_struct_0(A_271),'#skF_2'(A_272,k2_pre_topc(A_271,k6_domain_1(u1_struct_0(A_271),C_273))))) = k2_pre_topc(A_271,k6_domain_1(u1_struct_0(A_271),C_273))
      | ~ m1_subset_1(C_273,u1_struct_0(A_271))
      | ~ m1_subset_1('#skF_2'(A_272,k2_pre_topc(A_271,k6_domain_1(u1_struct_0(A_271),C_273))),u1_struct_0(A_271))
      | ~ l1_pre_topc(A_271)
      | ~ v3_tdlat_3(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271)
      | r1_xboole_0(A_272,k2_pre_topc(A_271,k6_domain_1(u1_struct_0(A_271),C_273))) ) ),
    inference(resolution,[status(thm)],[c_8,c_833])).

tff(c_2026,plain,(
    ! [A_272] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'(A_272,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))) = k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_2'(A_272,k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_xboole_0(A_272,k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_1957])).

tff(c_2036,plain,(
    ! [A_272] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'(A_272,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))) = k2_pre_topc('#skF_3',k1_tarski('#skF_5'))
      | ~ m1_subset_1('#skF_2'(A_272,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r1_xboole_0(A_272,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_44,c_42,c_40,c_499,c_36,c_499,c_2026])).

tff(c_3659,plain,(
    ! [A_335] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'(A_335,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))))) = k2_pre_topc('#skF_3',k1_tarski('#skF_5'))
      | ~ m1_subset_1('#skF_2'(A_335,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3'))
      | r1_xboole_0(A_335,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2036])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2216,plain,(
    ! [A_274,C_275,B_276] :
      ( k2_pre_topc(A_274,k6_domain_1(u1_struct_0(A_274),'#skF_2'(k2_pre_topc(A_274,k6_domain_1(u1_struct_0(A_274),C_275)),B_276))) = k2_pre_topc(A_274,k6_domain_1(u1_struct_0(A_274),C_275))
      | ~ m1_subset_1(C_275,u1_struct_0(A_274))
      | ~ m1_subset_1('#skF_2'(k2_pre_topc(A_274,k6_domain_1(u1_struct_0(A_274),C_275)),B_276),u1_struct_0(A_274))
      | ~ l1_pre_topc(A_274)
      | ~ v3_tdlat_3(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274)
      | r1_xboole_0(k2_pre_topc(A_274,k6_domain_1(u1_struct_0(A_274),C_275)),B_276) ) ),
    inference(resolution,[status(thm)],[c_10,c_833])).

tff(c_2307,plain,(
    ! [B_276] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),B_276))) = k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),B_276),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_xboole_0(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4')),B_276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_2216])).

tff(c_2326,plain,(
    ! [B_276] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),B_276))) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),B_276),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),B_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_44,c_42,c_40,c_508,c_38,c_508,c_2307])).

tff(c_2327,plain,(
    ! [B_276] :
      ( k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),B_276))) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
      | ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),B_276),u1_struct_0('#skF_3'))
      | r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),B_276) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2326])).

tff(c_3670,plain,
    ( k2_pre_topc('#skF_3',k1_tarski('#skF_5')) = k2_pre_topc('#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3'))
    | r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5')))
    | ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3'))
    | r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3659,c_2327])).

tff(c_3731,plain,
    ( ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_544,c_526,c_3670])).

tff(c_14579,plain,(
    ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3731])).

tff(c_14582,plain,(
    r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_3838,c_14579])).

tff(c_14595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_14582])).

tff(c_14596,plain,(
    ~ m1_subset_1('#skF_2'(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3731])).

tff(c_14600,plain,(
    r1_xboole_0(k2_pre_topc('#skF_3',k1_tarski('#skF_4')),k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_3838,c_14596])).

tff(c_14613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_14600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.48/5.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.48/5.15  
% 13.48/5.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.48/5.16  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 13.48/5.16  
% 13.48/5.16  %Foreground sorts:
% 13.48/5.16  
% 13.48/5.16  
% 13.48/5.16  %Background operators:
% 13.48/5.16  
% 13.48/5.16  
% 13.48/5.16  %Foreground operators:
% 13.48/5.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.48/5.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.48/5.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.48/5.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.48/5.16  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 13.48/5.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.48/5.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.48/5.16  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 13.48/5.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.48/5.16  tff('#skF_5', type, '#skF_5': $i).
% 13.48/5.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.48/5.16  tff('#skF_3', type, '#skF_3': $i).
% 13.48/5.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.48/5.16  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 13.48/5.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.48/5.16  tff('#skF_4', type, '#skF_4': $i).
% 13.48/5.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.48/5.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.48/5.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.48/5.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.48/5.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.48/5.16  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 13.48/5.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.48/5.16  
% 13.48/5.18  tff(f_149, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 13.48/5.18  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 13.48/5.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.48/5.18  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 13.48/5.18  tff(f_98, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 13.48/5.18  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 13.48/5.18  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.48/5.18  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 13.48/5.18  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 13.48/5.18  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 13.48/5.18  tff(f_74, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 13.48/5.18  tff(f_129, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 13.48/5.18  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.48/5.18  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.48/5.18  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.48/5.18  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.48/5.18  tff(c_162, plain, (![B_74, A_75]: (r2_hidden(B_74, k1_connsp_2(A_75, B_74)) | ~m1_subset_1(B_74, u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.48/5.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.48/5.18  tff(c_278, plain, (![A_93, B_94]: (~v1_xboole_0(k1_connsp_2(A_93, B_94)) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_162, c_2])).
% 13.48/5.18  tff(c_293, plain, (~v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_278])).
% 13.48/5.18  tff(c_302, plain, (~v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_293])).
% 13.48/5.18  tff(c_303, plain, (~v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_302])).
% 13.48/5.18  tff(c_104, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.48/5.18  tff(c_115, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_104])).
% 13.48/5.18  tff(c_117, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_115])).
% 13.48/5.18  tff(c_237, plain, (![A_89, B_90]: (m1_subset_1(k1_connsp_2(A_89, B_90), k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.48/5.18  tff(c_16, plain, (![B_15, A_13]: (v1_xboole_0(B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.48/5.18  tff(c_472, plain, (![A_120, B_121]: (v1_xboole_0(k1_connsp_2(A_120, B_121)) | ~v1_xboole_0(u1_struct_0(A_120)) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_237, c_16])).
% 13.48/5.18  tff(c_487, plain, (v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5')) | ~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_472])).
% 13.48/5.18  tff(c_496, plain, (v1_xboole_0(k1_connsp_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_117, c_487])).
% 13.48/5.18  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_303, c_496])).
% 13.48/5.18  tff(c_500, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_115])).
% 13.48/5.18  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.48/5.18  tff(c_116, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_104])).
% 13.48/5.18  tff(c_508, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_500, c_116])).
% 13.48/5.18  tff(c_499, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_115])).
% 13.48/5.18  tff(c_34, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.48/5.18  tff(c_502, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_34])).
% 13.48/5.18  tff(c_544, plain, (~r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_502])).
% 13.48/5.18  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.48/5.18  tff(c_18, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.48/5.18  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(k1_tarski(A_11), k1_zfmisc_1(B_12)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.48/5.18  tff(c_69, plain, (![A_51, B_52]: (r2_hidden('#skF_2'(A_51, B_52), B_52) | r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.48/5.18  tff(c_73, plain, (![B_52, A_51]: (~v1_xboole_0(B_52) | r1_xboole_0(A_51, B_52))), inference(resolution, [status(thm)], [c_69, c_2])).
% 13.48/5.18  tff(c_102, plain, (~v1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))), inference(resolution, [status(thm)], [c_73, c_34])).
% 13.48/5.18  tff(c_501, plain, (~v1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_102])).
% 13.48/5.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.48/5.18  tff(c_514, plain, (![A_122, B_123]: (m1_subset_1(k2_pre_topc(A_122, B_123), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.48/5.18  tff(c_20, plain, (![A_18, C_20, B_19]: (m1_subset_1(A_18, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.48/5.18  tff(c_793, plain, (![A_164, A_165, B_166]: (m1_subset_1(A_164, u1_struct_0(A_165)) | ~r2_hidden(A_164, k2_pre_topc(A_165, B_166)) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(resolution, [status(thm)], [c_514, c_20])).
% 13.48/5.18  tff(c_809, plain, (![A_165, B_166]: (m1_subset_1('#skF_1'(k2_pre_topc(A_165, B_166)), u1_struct_0(A_165)) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165) | v1_xboole_0(k2_pre_topc(A_165, B_166)))), inference(resolution, [status(thm)], [c_4, c_793])).
% 13.48/5.18  tff(c_42, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.48/5.18  tff(c_833, plain, (![A_169, C_170, B_171]: (k2_pre_topc(A_169, k6_domain_1(u1_struct_0(A_169), C_170))=k2_pre_topc(A_169, k6_domain_1(u1_struct_0(A_169), B_171)) | ~r2_hidden(B_171, k2_pre_topc(A_169, k6_domain_1(u1_struct_0(A_169), C_170))) | ~m1_subset_1(C_170, u1_struct_0(A_169)) | ~m1_subset_1(B_171, u1_struct_0(A_169)) | ~l1_pre_topc(A_169) | ~v3_tdlat_3(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.48/5.18  tff(c_1836, plain, (![A_269, C_270]: (k2_pre_topc(A_269, k6_domain_1(u1_struct_0(A_269), '#skF_1'(k2_pre_topc(A_269, k6_domain_1(u1_struct_0(A_269), C_270)))))=k2_pre_topc(A_269, k6_domain_1(u1_struct_0(A_269), C_270)) | ~m1_subset_1(C_270, u1_struct_0(A_269)) | ~m1_subset_1('#skF_1'(k2_pre_topc(A_269, k6_domain_1(u1_struct_0(A_269), C_270))), u1_struct_0(A_269)) | ~l1_pre_topc(A_269) | ~v3_tdlat_3(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269) | v1_xboole_0(k2_pre_topc(A_269, k6_domain_1(u1_struct_0(A_269), C_270))))), inference(resolution, [status(thm)], [c_4, c_833])).
% 13.48/5.18  tff(c_1895, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))))=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_499, c_1836])).
% 13.48/5.18  tff(c_1907, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))))=k2_pre_topc('#skF_3', k1_tarski('#skF_5')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_44, c_42, c_40, c_499, c_36, c_499, c_1895])).
% 13.48/5.18  tff(c_1908, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))))=k2_pre_topc('#skF_3', k1_tarski('#skF_5')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_501, c_46, c_1907])).
% 13.48/5.18  tff(c_2169, plain, (~m1_subset_1('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1908])).
% 13.48/5.18  tff(c_2172, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | v1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_809, c_2169])).
% 13.48/5.18  tff(c_2175, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2172])).
% 13.48/5.18  tff(c_2176, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_501, c_2175])).
% 13.48/5.18  tff(c_2180, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_2176])).
% 13.48/5.18  tff(c_2183, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_2180])).
% 13.48/5.18  tff(c_2186, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2183])).
% 13.48/5.18  tff(c_2188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_500, c_2186])).
% 13.48/5.18  tff(c_2190, plain, (m1_subset_1('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1908])).
% 13.48/5.18  tff(c_24, plain, (![A_23, B_24]: (k6_domain_1(A_23, B_24)=k1_tarski(B_24) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.48/5.18  tff(c_2201, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))))=k1_tarski('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2190, c_24])).
% 13.48/5.18  tff(c_2215, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))))=k1_tarski('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_500, c_2201])).
% 13.48/5.18  tff(c_2189, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))))=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_1908])).
% 13.48/5.18  tff(c_2400, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))))=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2215, c_2189])).
% 13.48/5.18  tff(c_22, plain, (![A_21, B_22]: (m1_subset_1(k2_pre_topc(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.48/5.18  tff(c_2455, plain, (m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k1_tarski('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2400, c_22])).
% 13.48/5.18  tff(c_2472, plain, (m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k1_tarski('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2455])).
% 13.48/5.18  tff(c_3599, plain, (~m1_subset_1(k1_tarski('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2472])).
% 13.48/5.18  tff(c_3603, plain, (~r2_hidden('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_3599])).
% 13.48/5.18  tff(c_3606, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_3603])).
% 13.48/5.18  tff(c_3609, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_3606])).
% 13.48/5.18  tff(c_3611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_500, c_3609])).
% 13.48/5.18  tff(c_3612, plain, (m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2472])).
% 13.48/5.18  tff(c_3818, plain, (![A_336]: (m1_subset_1(A_336, u1_struct_0('#skF_3')) | ~r2_hidden(A_336, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))))), inference(resolution, [status(thm)], [c_3612, c_20])).
% 13.48/5.18  tff(c_3838, plain, (![A_5]: (m1_subset_1('#skF_2'(A_5, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3')) | r1_xboole_0(A_5, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))))), inference(resolution, [status(thm)], [c_8, c_3818])).
% 13.48/5.18  tff(c_32, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.48/5.18  tff(c_503, plain, (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_32])).
% 13.48/5.18  tff(c_526, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_503])).
% 13.48/5.18  tff(c_1957, plain, (![A_271, A_272, C_273]: (k2_pre_topc(A_271, k6_domain_1(u1_struct_0(A_271), '#skF_2'(A_272, k2_pre_topc(A_271, k6_domain_1(u1_struct_0(A_271), C_273)))))=k2_pre_topc(A_271, k6_domain_1(u1_struct_0(A_271), C_273)) | ~m1_subset_1(C_273, u1_struct_0(A_271)) | ~m1_subset_1('#skF_2'(A_272, k2_pre_topc(A_271, k6_domain_1(u1_struct_0(A_271), C_273))), u1_struct_0(A_271)) | ~l1_pre_topc(A_271) | ~v3_tdlat_3(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271) | r1_xboole_0(A_272, k2_pre_topc(A_271, k6_domain_1(u1_struct_0(A_271), C_273))))), inference(resolution, [status(thm)], [c_8, c_833])).
% 13.48/5.18  tff(c_2026, plain, (![A_272]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'(A_272, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))))=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_2'(A_272, k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | r1_xboole_0(A_272, k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_499, c_1957])).
% 13.48/5.18  tff(c_2036, plain, (![A_272]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'(A_272, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))))=k2_pre_topc('#skF_3', k1_tarski('#skF_5')) | ~m1_subset_1('#skF_2'(A_272, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | r1_xboole_0(A_272, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_44, c_42, c_40, c_499, c_36, c_499, c_2026])).
% 13.48/5.18  tff(c_3659, plain, (![A_335]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'(A_335, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))))=k2_pre_topc('#skF_3', k1_tarski('#skF_5')) | ~m1_subset_1('#skF_2'(A_335, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3')) | r1_xboole_0(A_335, k2_pre_topc('#skF_3', k1_tarski('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_2036])).
% 13.48/5.18  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.48/5.18  tff(c_2216, plain, (![A_274, C_275, B_276]: (k2_pre_topc(A_274, k6_domain_1(u1_struct_0(A_274), '#skF_2'(k2_pre_topc(A_274, k6_domain_1(u1_struct_0(A_274), C_275)), B_276)))=k2_pre_topc(A_274, k6_domain_1(u1_struct_0(A_274), C_275)) | ~m1_subset_1(C_275, u1_struct_0(A_274)) | ~m1_subset_1('#skF_2'(k2_pre_topc(A_274, k6_domain_1(u1_struct_0(A_274), C_275)), B_276), u1_struct_0(A_274)) | ~l1_pre_topc(A_274) | ~v3_tdlat_3(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274) | r1_xboole_0(k2_pre_topc(A_274, k6_domain_1(u1_struct_0(A_274), C_275)), B_276))), inference(resolution, [status(thm)], [c_10, c_833])).
% 13.48/5.18  tff(c_2307, plain, (![B_276]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), B_276)))=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), B_276), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | r1_xboole_0(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')), B_276))), inference(superposition, [status(thm), theory('equality')], [c_508, c_2216])).
% 13.48/5.18  tff(c_2326, plain, (![B_276]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), B_276)))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), B_276), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), B_276))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_44, c_42, c_40, c_508, c_38, c_508, c_2307])).
% 13.48/5.18  tff(c_2327, plain, (![B_276]: (k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), B_276)))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), B_276), u1_struct_0('#skF_3')) | r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), B_276))), inference(negUnitSimplification, [status(thm)], [c_46, c_2326])).
% 13.48/5.18  tff(c_3670, plain, (k2_pre_topc('#skF_3', k1_tarski('#skF_5'))=k2_pre_topc('#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3')) | r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5'))) | ~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3')) | r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_3659, c_2327])).
% 13.48/5.18  tff(c_3731, plain, (~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_544, c_544, c_526, c_3670])).
% 13.48/5.18  tff(c_14579, plain, (~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_3731])).
% 13.48/5.18  tff(c_14582, plain, (r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_3838, c_14579])).
% 13.48/5.18  tff(c_14595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_544, c_14582])).
% 13.48/5.18  tff(c_14596, plain, (~m1_subset_1('#skF_2'(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5'))), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_3731])).
% 13.48/5.18  tff(c_14600, plain, (r1_xboole_0(k2_pre_topc('#skF_3', k1_tarski('#skF_4')), k2_pre_topc('#skF_3', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_3838, c_14596])).
% 13.48/5.18  tff(c_14613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_544, c_14600])).
% 13.48/5.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.48/5.18  
% 13.48/5.18  Inference rules
% 13.48/5.18  ----------------------
% 13.48/5.18  #Ref     : 0
% 13.48/5.18  #Sup     : 2941
% 13.48/5.18  #Fact    : 0
% 13.48/5.18  #Define  : 0
% 13.48/5.18  #Split   : 17
% 13.48/5.18  #Chain   : 0
% 13.48/5.18  #Close   : 0
% 13.48/5.18  
% 13.48/5.18  Ordering : KBO
% 13.48/5.18  
% 13.48/5.18  Simplification rules
% 13.48/5.18  ----------------------
% 13.48/5.18  #Subsume      : 176
% 13.48/5.18  #Demod        : 4205
% 13.48/5.18  #Tautology    : 420
% 13.48/5.18  #SimpNegUnit  : 1143
% 13.48/5.18  #BackRed      : 6
% 13.48/5.18  
% 13.48/5.18  #Partial instantiations: 0
% 13.48/5.18  #Strategies tried      : 1
% 13.48/5.18  
% 13.48/5.18  Timing (in seconds)
% 13.48/5.18  ----------------------
% 13.48/5.18  Preprocessing        : 0.32
% 13.48/5.18  Parsing              : 0.18
% 13.48/5.18  CNF conversion       : 0.02
% 13.48/5.18  Main loop            : 4.14
% 13.48/5.18  Inferencing          : 0.91
% 13.48/5.18  Reduction            : 1.17
% 13.48/5.18  Demodulation         : 0.84
% 13.48/5.18  BG Simplification    : 0.13
% 13.48/5.18  Subsumption          : 1.72
% 13.48/5.18  Abstraction          : 0.21
% 13.48/5.18  MUC search           : 0.00
% 13.48/5.18  Cooper               : 0.00
% 13.48/5.18  Total                : 4.50
% 13.48/5.18  Index Insertion      : 0.00
% 13.48/5.18  Index Deletion       : 0.00
% 13.48/5.18  Index Matching       : 0.00
% 13.48/5.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
