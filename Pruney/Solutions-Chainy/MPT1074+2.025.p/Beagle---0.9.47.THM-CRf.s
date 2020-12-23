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
% DateTime   : Thu Dec  3 10:18:09 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 542 expanded)
%              Number of leaves         :   34 ( 203 expanded)
%              Depth                    :   26
%              Number of atoms          :  178 (1762 expanded)
%              Number of equality atoms :   22 ( 101 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_129,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_143,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_34,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_144,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_34])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_69,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_322,plain,(
    ! [C_95,B_96] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_95),B_96,C_95),k1_relat_1(C_95))
      | v1_funct_2(C_95,k1_relat_1(C_95),B_96)
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_84,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_84])).

tff(c_251,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1(k1_relset_1(A_87,B_88,C_89),k1_zfmisc_1(A_87))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_273,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_251])).

tff(c_281,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_273])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_290,plain,(
    ! [A_3] :
      ( m1_subset_1(A_3,'#skF_3')
      | ~ r2_hidden(A_3,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_281,c_6])).

tff(c_326,plain,(
    ! [B_96] :
      ( m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_96,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_96)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_322,c_290])).

tff(c_331,plain,(
    ! [B_96] :
      ( m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_96,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_42,c_326])).

tff(c_616,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k3_funct_2(A_145,B_146,C_147,D_148) = k1_funct_1(C_147,D_148)
      | ~ m1_subset_1(D_148,A_145)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_2(C_147,A_145,B_146)
      | ~ v1_funct_1(C_147)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_630,plain,(
    ! [B_146,C_147,B_96] :
      ( k3_funct_2('#skF_3',B_146,C_147,'#skF_1'(k1_relat_1('#skF_5'),B_96,'#skF_5')) = k1_funct_1(C_147,'#skF_1'(k1_relat_1('#skF_5'),B_96,'#skF_5'))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_146)))
      | ~ v1_funct_2(C_147,'#skF_3',B_146)
      | ~ v1_funct_1(C_147)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_96) ) ),
    inference(resolution,[status(thm)],[c_331,c_616])).

tff(c_697,plain,(
    ! [B_153,C_154,B_155] :
      ( k3_funct_2('#skF_3',B_153,C_154,'#skF_1'(k1_relat_1('#skF_5'),B_155,'#skF_5')) = k1_funct_1(C_154,'#skF_1'(k1_relat_1('#skF_5'),B_155,'#skF_5'))
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_153)))
      | ~ v1_funct_2(C_154,'#skF_3',B_153)
      | ~ v1_funct_1(C_154)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_630])).

tff(c_711,plain,(
    ! [B_155] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),B_155,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),B_155,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_155) ) ),
    inference(resolution,[status(thm)],[c_38,c_697])).

tff(c_1087,plain,(
    ! [B_230] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),B_230,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),B_230,'#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_711])).

tff(c_36,plain,(
    ! [E_42] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_42),'#skF_2')
      | ~ m1_subset_1(E_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1113,plain,(
    ! [B_231] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),B_231,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_231,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_36])).

tff(c_26,plain,(
    ! [C_29,B_28] :
      ( ~ r2_hidden(k1_funct_1(C_29,'#skF_1'(k1_relat_1(C_29),B_28,C_29)),B_28)
      | v1_funct_2(C_29,k1_relat_1(C_29),B_28)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1121,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1113,c_26])).

tff(c_1129,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_42,c_1121])).

tff(c_1131,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1129])).

tff(c_460,plain,(
    ! [C_126,B_127] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_126),B_127,C_126),k1_relat_1(C_126))
      | m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_126),B_127)))
      | ~ v1_funct_1(C_126)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_464,plain,(
    ! [B_127] :
      ( m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_127,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_127)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_460,c_290])).

tff(c_471,plain,(
    ! [B_128] :
      ( m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_128,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_128))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_42,c_464])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] :
      ( k2_relset_1(A_20,B_21,C_22) = k2_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_500,plain,(
    ! [B_128] :
      ( k2_relset_1(k1_relat_1('#skF_5'),B_128,'#skF_5') = k2_relat_1('#skF_5')
      | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_128,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_471,c_18])).

tff(c_1155,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_500,c_1131])).

tff(c_155,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k2_relset_1(A_75,B_76,C_77),k1_zfmisc_1(B_76))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_179,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(k2_relset_1(A_75,B_76,C_77),B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_499,plain,(
    ! [B_128] :
      ( r1_tarski(k2_relset_1(k1_relat_1('#skF_5'),B_128,'#skF_5'),B_128)
      | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_128,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_471,c_179])).

tff(c_1234,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1155,c_499])).

tff(c_1246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1131,c_144,c_1234])).

tff(c_1248,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1129])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k3_funct_2(A_23,B_24,C_25,D_26) = k1_funct_1(C_25,D_26)
      | ~ m1_subset_1(D_26,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1250,plain,(
    ! [B_24,C_25] :
      ( k3_funct_2('#skF_3',B_24,C_25,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_25,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_24)))
      | ~ v1_funct_2(C_25,'#skF_3',B_24)
      | ~ v1_funct_1(C_25)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1248,c_20])).

tff(c_1717,plain,(
    ! [B_255,C_256] :
      ( k3_funct_2('#skF_3',B_255,C_256,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_256,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_255)))
      | ~ v1_funct_2(C_256,'#skF_3',B_255)
      | ~ v1_funct_1(C_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1250])).

tff(c_1756,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1717])).

tff(c_1768,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1756])).

tff(c_1789,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_36])).

tff(c_1808,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_1789])).

tff(c_22,plain,(
    ! [C_29,B_28] :
      ( ~ r2_hidden(k1_funct_1(C_29,'#skF_1'(k1_relat_1(C_29),B_28,C_29)),B_28)
      | m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_29),B_28)))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1814,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1808,c_22])).

tff(c_1822,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_42,c_1814])).

tff(c_1858,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1822,c_18])).

tff(c_1857,plain,(
    r1_tarski(k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1822,c_179])).

tff(c_1928,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1858,c_1857])).

tff(c_1930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_1928])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n004.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:05:53 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.76  
% 4.10/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.76  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.10/1.76  
% 4.10/1.76  %Foreground sorts:
% 4.10/1.76  
% 4.10/1.76  
% 4.10/1.76  %Background operators:
% 4.10/1.76  
% 4.10/1.76  
% 4.10/1.76  %Foreground operators:
% 4.10/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.10/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.10/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.10/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.10/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.10/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.10/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.10/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.10/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.10/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.10/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.10/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.10/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.10/1.76  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.10/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.10/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.76  
% 4.50/1.78  tff(f_112, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 4.50/1.78  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.50/1.78  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.50/1.78  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.50/1.78  tff(f_90, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 4.50/1.78  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.50/1.78  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.50/1.78  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.50/1.78  tff(f_73, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.50/1.78  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.50/1.78  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.50/1.78  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.50/1.78  tff(c_129, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.50/1.78  tff(c_143, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_129])).
% 4.50/1.78  tff(c_34, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.50/1.78  tff(c_144, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_34])).
% 4.50/1.78  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.50/1.78  tff(c_59, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.50/1.78  tff(c_65, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_59])).
% 4.50/1.78  tff(c_69, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_65])).
% 4.50/1.78  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.50/1.78  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.50/1.78  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.50/1.78  tff(c_322, plain, (![C_95, B_96]: (r2_hidden('#skF_1'(k1_relat_1(C_95), B_96, C_95), k1_relat_1(C_95)) | v1_funct_2(C_95, k1_relat_1(C_95), B_96) | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.50/1.78  tff(c_84, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/1.78  tff(c_93, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_84])).
% 4.50/1.78  tff(c_251, plain, (![A_87, B_88, C_89]: (m1_subset_1(k1_relset_1(A_87, B_88, C_89), k1_zfmisc_1(A_87)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.50/1.78  tff(c_273, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_251])).
% 4.50/1.78  tff(c_281, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_273])).
% 4.50/1.78  tff(c_6, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.50/1.78  tff(c_290, plain, (![A_3]: (m1_subset_1(A_3, '#skF_3') | ~r2_hidden(A_3, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_281, c_6])).
% 4.50/1.78  tff(c_326, plain, (![B_96]: (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_96, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_96) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_322, c_290])).
% 4.50/1.78  tff(c_331, plain, (![B_96]: (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_96, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_96))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_42, c_326])).
% 4.50/1.78  tff(c_616, plain, (![A_145, B_146, C_147, D_148]: (k3_funct_2(A_145, B_146, C_147, D_148)=k1_funct_1(C_147, D_148) | ~m1_subset_1(D_148, A_145) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_2(C_147, A_145, B_146) | ~v1_funct_1(C_147) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.78  tff(c_630, plain, (![B_146, C_147, B_96]: (k3_funct_2('#skF_3', B_146, C_147, '#skF_1'(k1_relat_1('#skF_5'), B_96, '#skF_5'))=k1_funct_1(C_147, '#skF_1'(k1_relat_1('#skF_5'), B_96, '#skF_5')) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_146))) | ~v1_funct_2(C_147, '#skF_3', B_146) | ~v1_funct_1(C_147) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_96))), inference(resolution, [status(thm)], [c_331, c_616])).
% 4.50/1.78  tff(c_697, plain, (![B_153, C_154, B_155]: (k3_funct_2('#skF_3', B_153, C_154, '#skF_1'(k1_relat_1('#skF_5'), B_155, '#skF_5'))=k1_funct_1(C_154, '#skF_1'(k1_relat_1('#skF_5'), B_155, '#skF_5')) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_153))) | ~v1_funct_2(C_154, '#skF_3', B_153) | ~v1_funct_1(C_154) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_155))), inference(negUnitSimplification, [status(thm)], [c_46, c_630])).
% 4.50/1.78  tff(c_711, plain, (![B_155]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), B_155, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), B_155, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_155))), inference(resolution, [status(thm)], [c_38, c_697])).
% 4.50/1.78  tff(c_1087, plain, (![B_230]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), B_230, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), B_230, '#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_230))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_711])).
% 4.50/1.78  tff(c_36, plain, (![E_42]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_42), '#skF_2') | ~m1_subset_1(E_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.50/1.78  tff(c_1113, plain, (![B_231]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), B_231, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_231, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_231))), inference(superposition, [status(thm), theory('equality')], [c_1087, c_36])).
% 4.50/1.78  tff(c_26, plain, (![C_29, B_28]: (~r2_hidden(k1_funct_1(C_29, '#skF_1'(k1_relat_1(C_29), B_28, C_29)), B_28) | v1_funct_2(C_29, k1_relat_1(C_29), B_28) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.50/1.78  tff(c_1121, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_1113, c_26])).
% 4.50/1.78  tff(c_1129, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_42, c_1121])).
% 4.50/1.78  tff(c_1131, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1129])).
% 4.50/1.78  tff(c_460, plain, (![C_126, B_127]: (r2_hidden('#skF_1'(k1_relat_1(C_126), B_127, C_126), k1_relat_1(C_126)) | m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_126), B_127))) | ~v1_funct_1(C_126) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.50/1.78  tff(c_464, plain, (![B_127]: (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_127, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_127))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_460, c_290])).
% 4.50/1.78  tff(c_471, plain, (![B_128]: (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_128, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_128))))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_42, c_464])).
% 4.50/1.78  tff(c_18, plain, (![A_20, B_21, C_22]: (k2_relset_1(A_20, B_21, C_22)=k2_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.50/1.78  tff(c_500, plain, (![B_128]: (k2_relset_1(k1_relat_1('#skF_5'), B_128, '#skF_5')=k2_relat_1('#skF_5') | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_128, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_471, c_18])).
% 4.50/1.78  tff(c_1155, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_500, c_1131])).
% 4.50/1.78  tff(c_155, plain, (![A_75, B_76, C_77]: (m1_subset_1(k2_relset_1(A_75, B_76, C_77), k1_zfmisc_1(B_76)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.50/1.78  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.78  tff(c_179, plain, (![A_75, B_76, C_77]: (r1_tarski(k2_relset_1(A_75, B_76, C_77), B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(resolution, [status(thm)], [c_155, c_2])).
% 4.50/1.78  tff(c_499, plain, (![B_128]: (r1_tarski(k2_relset_1(k1_relat_1('#skF_5'), B_128, '#skF_5'), B_128) | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_128, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_471, c_179])).
% 4.50/1.78  tff(c_1234, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1155, c_499])).
% 4.50/1.78  tff(c_1246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1131, c_144, c_1234])).
% 4.50/1.78  tff(c_1248, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_1129])).
% 4.50/1.78  tff(c_20, plain, (![A_23, B_24, C_25, D_26]: (k3_funct_2(A_23, B_24, C_25, D_26)=k1_funct_1(C_25, D_26) | ~m1_subset_1(D_26, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.78  tff(c_1250, plain, (![B_24, C_25]: (k3_funct_2('#skF_3', B_24, C_25, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_25, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_24))) | ~v1_funct_2(C_25, '#skF_3', B_24) | ~v1_funct_1(C_25) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_1248, c_20])).
% 4.50/1.78  tff(c_1717, plain, (![B_255, C_256]: (k3_funct_2('#skF_3', B_255, C_256, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_256, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_255))) | ~v1_funct_2(C_256, '#skF_3', B_255) | ~v1_funct_1(C_256))), inference(negUnitSimplification, [status(thm)], [c_46, c_1250])).
% 4.50/1.78  tff(c_1756, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_1717])).
% 4.50/1.78  tff(c_1768, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1756])).
% 4.50/1.78  tff(c_1789, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1768, c_36])).
% 4.50/1.78  tff(c_1808, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_1789])).
% 4.50/1.78  tff(c_22, plain, (![C_29, B_28]: (~r2_hidden(k1_funct_1(C_29, '#skF_1'(k1_relat_1(C_29), B_28, C_29)), B_28) | m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_29), B_28))) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.50/1.78  tff(c_1814, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1808, c_22])).
% 4.50/1.78  tff(c_1822, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_42, c_1814])).
% 4.50/1.78  tff(c_1858, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1822, c_18])).
% 4.50/1.78  tff(c_1857, plain, (r1_tarski(k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_1822, c_179])).
% 4.50/1.78  tff(c_1928, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1858, c_1857])).
% 4.50/1.78  tff(c_1930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_1928])).
% 4.50/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.78  
% 4.50/1.78  Inference rules
% 4.50/1.78  ----------------------
% 4.50/1.78  #Ref     : 0
% 4.50/1.78  #Sup     : 424
% 4.50/1.78  #Fact    : 0
% 4.50/1.78  #Define  : 0
% 4.50/1.78  #Split   : 6
% 4.50/1.78  #Chain   : 0
% 4.50/1.78  #Close   : 0
% 4.50/1.78  
% 4.50/1.78  Ordering : KBO
% 4.50/1.78  
% 4.50/1.78  Simplification rules
% 4.50/1.78  ----------------------
% 4.50/1.78  #Subsume      : 32
% 4.50/1.78  #Demod        : 70
% 4.50/1.78  #Tautology    : 32
% 4.50/1.78  #SimpNegUnit  : 10
% 4.50/1.78  #BackRed      : 2
% 4.50/1.78  
% 4.50/1.78  #Partial instantiations: 0
% 4.50/1.78  #Strategies tried      : 1
% 4.50/1.78  
% 4.50/1.78  Timing (in seconds)
% 4.50/1.78  ----------------------
% 4.50/1.78  Preprocessing        : 0.33
% 4.50/1.78  Parsing              : 0.18
% 4.50/1.78  CNF conversion       : 0.02
% 4.50/1.78  Main loop            : 0.69
% 4.57/1.78  Inferencing          : 0.25
% 4.57/1.78  Reduction            : 0.19
% 4.57/1.78  Demodulation         : 0.14
% 4.57/1.78  BG Simplification    : 0.04
% 4.57/1.78  Subsumption          : 0.14
% 4.57/1.78  Abstraction          : 0.05
% 4.57/1.78  MUC search           : 0.00
% 4.57/1.78  Cooper               : 0.00
% 4.57/1.78  Total                : 1.06
% 4.57/1.78  Index Insertion      : 0.00
% 4.57/1.78  Index Deletion       : 0.00
% 4.57/1.78  Index Matching       : 0.00
% 4.57/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
