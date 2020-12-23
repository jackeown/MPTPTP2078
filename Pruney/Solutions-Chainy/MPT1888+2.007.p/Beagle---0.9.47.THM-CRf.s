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
% DateTime   : Thu Dec  3 10:30:21 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 496 expanded)
%              Number of leaves         :   39 ( 180 expanded)
%              Depth                    :   19
%              Number of atoms          :  193 (1554 expanded)
%              Number of equality atoms :   22 ( 253 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_xboole_0(B,C)
                  & v3_pre_topc(B,A) )
               => r1_xboole_0(B,k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

tff(c_54,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_24,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_92,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(A_57,B_58) = k1_tarski(B_58)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_99,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_92])).

tff(c_109,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_26,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_112,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_109,c_26])).

tff(c_115,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_112])).

tff(c_118,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_115])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_118])).

tff(c_124,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_100,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_130,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_100])).

tff(c_123,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_46,plain,(
    k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) != k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_125,plain,(
    k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')) != k2_pre_topc('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_46])).

tff(c_137,plain,(
    k2_pre_topc('#skF_5',k1_tarski('#skF_7')) != k2_pre_topc('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_125])).

tff(c_58,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_56,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_140,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k6_domain_1(A_67,B_68),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_140])).

tff(c_152,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_146])).

tff(c_153,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_152])).

tff(c_269,plain,(
    ! [A_90,B_91] :
      ( v4_pre_topc(k2_pre_topc(A_90,B_91),A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_277,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_153,c_269])).

tff(c_288,plain,(
    v4_pre_topc(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_277])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k2_pre_topc(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_149,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_140])).

tff(c_155,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_149])).

tff(c_156,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_155])).

tff(c_319,plain,(
    ! [B_95,A_96,C_97] :
      ( r1_xboole_0(B_95,k2_pre_topc(A_96,C_97))
      | ~ v3_pre_topc(B_95,A_96)
      | ~ r1_xboole_0(B_95,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_325,plain,(
    ! [B_95] :
      ( r1_xboole_0(B_95,k2_pre_topc('#skF_5',k1_tarski('#skF_7')))
      | ~ v3_pre_topc(B_95,'#skF_5')
      | ~ r1_xboole_0(B_95,k1_tarski('#skF_7'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_156,c_319])).

tff(c_434,plain,(
    ! [B_105] :
      ( r1_xboole_0(B_105,k2_pre_topc('#skF_5',k1_tarski('#skF_7')))
      | ~ v3_pre_topc(B_105,'#skF_5')
      | ~ r1_xboole_0(B_105,k1_tarski('#skF_7'))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_325])).

tff(c_48,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6')),k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_139,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k2_pre_topc('#skF_5',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_123,c_48])).

tff(c_440,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | ~ r1_xboole_0(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_7'))
    | ~ m1_subset_1(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_434,c_139])).

tff(c_1547,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_1550,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1547])).

tff(c_1554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_153,c_1550])).

tff(c_1556,plain,(
    m1_subset_1(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_34,plain,(
    ! [B_25,A_22] :
      ( v3_pre_topc(B_25,A_22)
      | ~ v4_pre_topc(B_25,A_22)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v3_tdlat_3(A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1561,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | ~ v4_pre_topc(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1556,c_34])).

tff(c_1572,plain,(
    v3_pre_topc(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_56,c_288,c_1561])).

tff(c_1555,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_7'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_1772,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_1555])).

tff(c_85,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),B_53)
      | r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_90,plain,(
    ! [A_52,A_6] :
      ( '#skF_1'(A_52,k1_tarski(A_6)) = A_6
      | r1_xboole_0(A_52,k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_1784,plain,(
    '#skF_1'(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_90,c_1772])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1909,plain,
    ( r2_hidden('#skF_7',k2_pre_topc('#skF_5',k1_tarski('#skF_6')))
    | r1_xboole_0(k2_pre_topc('#skF_5',k1_tarski('#skF_6')),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1784,c_6])).

tff(c_1932,plain,(
    r2_hidden('#skF_7',k2_pre_topc('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1772,c_1909])).

tff(c_616,plain,(
    ! [A_117,C_118,B_119] :
      ( k2_pre_topc(A_117,k6_domain_1(u1_struct_0(A_117),C_118)) = k2_pre_topc(A_117,k6_domain_1(u1_struct_0(A_117),B_119))
      | ~ r2_hidden(B_119,k2_pre_topc(A_117,k6_domain_1(u1_struct_0(A_117),C_118)))
      | ~ m1_subset_1(C_118,u1_struct_0(A_117))
      | ~ m1_subset_1(B_119,u1_struct_0(A_117))
      | ~ l1_pre_topc(A_117)
      | ~ v3_tdlat_3(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_627,plain,(
    ! [B_119] :
      ( k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_119)) = k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'))
      | ~ r2_hidden(B_119,k2_pre_topc('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_616])).

tff(c_642,plain,(
    ! [B_119] :
      ( k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_119)) = k2_pre_topc('#skF_5',k1_tarski('#skF_6'))
      | ~ r2_hidden(B_119,k2_pre_topc('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_130,c_627])).

tff(c_643,plain,(
    ! [B_119] :
      ( k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),B_119)) = k2_pre_topc('#skF_5',k1_tarski('#skF_6'))
      | ~ r2_hidden(B_119,k2_pre_topc('#skF_5',k1_tarski('#skF_6')))
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_642])).

tff(c_1937,plain,
    ( k2_pre_topc('#skF_5',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) = k2_pre_topc('#skF_5',k1_tarski('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1932,c_643])).

tff(c_1940,plain,(
    k2_pre_topc('#skF_5',k1_tarski('#skF_7')) = k2_pre_topc('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_123,c_1937])).

tff(c_1942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_1940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:06:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.73  
% 3.85/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.74  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.85/1.74  
% 3.85/1.74  %Foreground sorts:
% 3.85/1.74  
% 3.85/1.74  
% 3.85/1.74  %Background operators:
% 3.85/1.74  
% 3.85/1.74  
% 3.85/1.74  %Foreground operators:
% 3.85/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.85/1.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.85/1.74  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.85/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.85/1.74  tff('#skF_7', type, '#skF_7': $i).
% 3.85/1.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.85/1.74  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.85/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.74  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.74  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.85/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.85/1.74  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.85/1.74  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.85/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.85/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.85/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.85/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.85/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.85/1.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.85/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.74  
% 3.85/1.75  tff(f_160, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tex_2)).
% 3.85/1.75  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.85/1.75  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.85/1.75  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.85/1.75  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.85/1.75  tff(f_92, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.85/1.75  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.85/1.75  tff(f_121, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_tsep_1)).
% 3.85/1.75  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.85/1.75  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.85/1.75  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.85/1.75  tff(f_140, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tex_2)).
% 3.85/1.75  tff(c_54, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.85/1.75  tff(c_24, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.75  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.85/1.75  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.85/1.75  tff(c_92, plain, (![A_57, B_58]: (k6_domain_1(A_57, B_58)=k1_tarski(B_58) | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.85/1.75  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_92])).
% 3.85/1.75  tff(c_109, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_99])).
% 3.85/1.75  tff(c_26, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.85/1.75  tff(c_112, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_109, c_26])).
% 3.85/1.75  tff(c_115, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_112])).
% 3.85/1.75  tff(c_118, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_115])).
% 3.85/1.75  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_118])).
% 3.85/1.75  tff(c_124, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_99])).
% 3.85/1.75  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.85/1.75  tff(c_100, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_92])).
% 3.85/1.75  tff(c_130, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_124, c_100])).
% 3.85/1.75  tff(c_123, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_99])).
% 3.85/1.75  tff(c_46, plain, (k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))!=k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.85/1.75  tff(c_125, plain, (k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'))!=k2_pre_topc('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_46])).
% 3.85/1.75  tff(c_137, plain, (k2_pre_topc('#skF_5', k1_tarski('#skF_7'))!=k2_pre_topc('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_125])).
% 3.85/1.75  tff(c_58, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.85/1.75  tff(c_56, plain, (v3_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.85/1.75  tff(c_140, plain, (![A_67, B_68]: (m1_subset_1(k6_domain_1(A_67, B_68), k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.75  tff(c_146, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_140])).
% 3.85/1.75  tff(c_152, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_146])).
% 3.85/1.75  tff(c_153, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_124, c_152])).
% 3.85/1.75  tff(c_269, plain, (![A_90, B_91]: (v4_pre_topc(k2_pre_topc(A_90, B_91), A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.85/1.75  tff(c_277, plain, (v4_pre_topc(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_153, c_269])).
% 3.85/1.75  tff(c_288, plain, (v4_pre_topc(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_277])).
% 3.85/1.75  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(k2_pre_topc(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.85/1.75  tff(c_149, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_140])).
% 3.85/1.75  tff(c_155, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_149])).
% 3.85/1.75  tff(c_156, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_124, c_155])).
% 3.85/1.75  tff(c_319, plain, (![B_95, A_96, C_97]: (r1_xboole_0(B_95, k2_pre_topc(A_96, C_97)) | ~v3_pre_topc(B_95, A_96) | ~r1_xboole_0(B_95, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.85/1.75  tff(c_325, plain, (![B_95]: (r1_xboole_0(B_95, k2_pre_topc('#skF_5', k1_tarski('#skF_7'))) | ~v3_pre_topc(B_95, '#skF_5') | ~r1_xboole_0(B_95, k1_tarski('#skF_7')) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_156, c_319])).
% 3.85/1.75  tff(c_434, plain, (![B_105]: (r1_xboole_0(B_105, k2_pre_topc('#skF_5', k1_tarski('#skF_7'))) | ~v3_pre_topc(B_105, '#skF_5') | ~r1_xboole_0(B_105, k1_tarski('#skF_7')) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_325])).
% 3.85/1.75  tff(c_48, plain, (~r1_xboole_0(k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')), k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.85/1.75  tff(c_139, plain, (~r1_xboole_0(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k2_pre_topc('#skF_5', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_123, c_48])).
% 3.85/1.75  tff(c_440, plain, (~v3_pre_topc(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), '#skF_5') | ~r1_xboole_0(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k1_tarski('#skF_7')) | ~m1_subset_1(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_434, c_139])).
% 3.85/1.75  tff(c_1547, plain, (~m1_subset_1(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_440])).
% 3.85/1.75  tff(c_1550, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1547])).
% 3.85/1.75  tff(c_1554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_153, c_1550])).
% 3.85/1.75  tff(c_1556, plain, (m1_subset_1(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_440])).
% 3.85/1.75  tff(c_34, plain, (![B_25, A_22]: (v3_pre_topc(B_25, A_22) | ~v4_pre_topc(B_25, A_22) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_22))) | ~v3_tdlat_3(A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.85/1.75  tff(c_1561, plain, (v3_pre_topc(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), '#skF_5') | ~v4_pre_topc(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), '#skF_5') | ~v3_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1556, c_34])).
% 3.85/1.75  tff(c_1572, plain, (v3_pre_topc(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_56, c_288, c_1561])).
% 3.85/1.75  tff(c_1555, plain, (~r1_xboole_0(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k1_tarski('#skF_7')) | ~v3_pre_topc(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), '#skF_5')), inference(splitRight, [status(thm)], [c_440])).
% 3.85/1.75  tff(c_1772, plain, (~r1_xboole_0(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_1555])).
% 3.85/1.75  tff(c_85, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), B_53) | r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.75  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.85/1.75  tff(c_90, plain, (![A_52, A_6]: ('#skF_1'(A_52, k1_tarski(A_6))=A_6 | r1_xboole_0(A_52, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_85, c_8])).
% 3.85/1.75  tff(c_1784, plain, ('#skF_1'(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_90, c_1772])).
% 3.85/1.75  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.75  tff(c_1909, plain, (r2_hidden('#skF_7', k2_pre_topc('#skF_5', k1_tarski('#skF_6'))) | r1_xboole_0(k2_pre_topc('#skF_5', k1_tarski('#skF_6')), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1784, c_6])).
% 3.85/1.75  tff(c_1932, plain, (r2_hidden('#skF_7', k2_pre_topc('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_1772, c_1909])).
% 3.85/1.75  tff(c_616, plain, (![A_117, C_118, B_119]: (k2_pre_topc(A_117, k6_domain_1(u1_struct_0(A_117), C_118))=k2_pre_topc(A_117, k6_domain_1(u1_struct_0(A_117), B_119)) | ~r2_hidden(B_119, k2_pre_topc(A_117, k6_domain_1(u1_struct_0(A_117), C_118))) | ~m1_subset_1(C_118, u1_struct_0(A_117)) | ~m1_subset_1(B_119, u1_struct_0(A_117)) | ~l1_pre_topc(A_117) | ~v3_tdlat_3(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.85/1.75  tff(c_627, plain, (![B_119]: (k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_119))=k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')) | ~r2_hidden(B_119, k2_pre_topc('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(B_119, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v3_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_616])).
% 3.85/1.75  tff(c_642, plain, (![B_119]: (k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_119))=k2_pre_topc('#skF_5', k1_tarski('#skF_6')) | ~r2_hidden(B_119, k2_pre_topc('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(B_119, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_130, c_627])).
% 3.85/1.75  tff(c_643, plain, (![B_119]: (k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), B_119))=k2_pre_topc('#skF_5', k1_tarski('#skF_6')) | ~r2_hidden(B_119, k2_pre_topc('#skF_5', k1_tarski('#skF_6'))) | ~m1_subset_1(B_119, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_642])).
% 3.85/1.75  tff(c_1937, plain, (k2_pre_topc('#skF_5', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))=k2_pre_topc('#skF_5', k1_tarski('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1932, c_643])).
% 3.85/1.75  tff(c_1940, plain, (k2_pre_topc('#skF_5', k1_tarski('#skF_7'))=k2_pre_topc('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_123, c_1937])).
% 3.85/1.75  tff(c_1942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_1940])).
% 3.85/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.75  
% 3.85/1.75  Inference rules
% 3.85/1.75  ----------------------
% 3.85/1.75  #Ref     : 0
% 3.85/1.75  #Sup     : 450
% 3.85/1.75  #Fact    : 0
% 3.85/1.75  #Define  : 0
% 3.85/1.75  #Split   : 5
% 3.85/1.75  #Chain   : 0
% 3.85/1.75  #Close   : 0
% 3.85/1.75  
% 3.85/1.75  Ordering : KBO
% 3.85/1.75  
% 3.85/1.75  Simplification rules
% 3.85/1.75  ----------------------
% 3.85/1.75  #Subsume      : 127
% 3.85/1.75  #Demod        : 162
% 3.85/1.75  #Tautology    : 177
% 3.85/1.75  #SimpNegUnit  : 21
% 3.85/1.75  #BackRed      : 1
% 3.85/1.75  
% 3.85/1.75  #Partial instantiations: 0
% 3.85/1.75  #Strategies tried      : 1
% 3.85/1.75  
% 3.85/1.75  Timing (in seconds)
% 3.85/1.75  ----------------------
% 3.85/1.76  Preprocessing        : 0.33
% 3.85/1.76  Parsing              : 0.17
% 3.85/1.76  CNF conversion       : 0.02
% 3.85/1.76  Main loop            : 0.65
% 3.85/1.76  Inferencing          : 0.22
% 3.85/1.76  Reduction            : 0.19
% 3.85/1.76  Demodulation         : 0.13
% 3.85/1.76  BG Simplification    : 0.03
% 3.85/1.76  Subsumption          : 0.14
% 3.85/1.76  Abstraction          : 0.03
% 3.85/1.76  MUC search           : 0.00
% 3.85/1.76  Cooper               : 0.00
% 3.85/1.76  Total                : 1.02
% 3.85/1.76  Index Insertion      : 0.00
% 3.85/1.76  Index Deletion       : 0.00
% 3.85/1.76  Index Matching       : 0.00
% 3.85/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
