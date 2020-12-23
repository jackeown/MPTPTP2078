%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:07 EST 2020

% Result     : Theorem 5.76s
% Output     : CNFRefutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :  140 (5058 expanded)
%              Number of leaves         :   40 (1751 expanded)
%              Depth                    :   30
%              Number of atoms          :  271 (19278 expanded)
%              Number of equality atoms :   52 (3028 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_148,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3357,plain,(
    ! [A_358,B_359] :
      ( m1_subset_1(A_358,B_359)
      | ~ r2_hidden(A_358,B_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3362,plain,(
    ! [A_360] :
      ( m1_subset_1('#skF_1'(A_360),A_360)
      | v1_xboole_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_4,c_3357])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_94,plain,(
    ! [E_69] :
      ( r2_hidden(k3_funct_2('#skF_9','#skF_10','#skF_11',E_69),'#skF_8')
      | ~ m1_subset_1(E_69,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [E_69] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ m1_subset_1(E_69,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_99,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_82,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_133,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    k2_relset_1('#skF_9','#skF_10','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_133])).

tff(c_78,plain,(
    ~ r1_tarski(k2_relset_1('#skF_9','#skF_10','#skF_11'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_143,plain,(
    ~ r1_tarski(k2_relat_1('#skF_11'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_78])).

tff(c_86,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_115,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_115])).

tff(c_84,plain,(
    v1_funct_2('#skF_11','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_499,plain,(
    ! [B_170,C_171,A_172] :
      ( k1_xboole_0 = B_170
      | r2_hidden(C_171,k1_funct_2(A_172,B_170))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_170)))
      | ~ v1_funct_2(C_171,A_172,B_170)
      | ~ v1_funct_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_522,plain,
    ( k1_xboole_0 = '#skF_10'
    | r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_10'))
    | ~ v1_funct_2('#skF_11','#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_499])).

tff(c_530,plain,
    ( k1_xboole_0 = '#skF_10'
    | r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_522])).

tff(c_531,plain,(
    r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_26,plain,(
    ! [A_15,B_16,D_31] :
      ( '#skF_5'(A_15,B_16,k1_funct_2(A_15,B_16),D_31) = D_31
      | ~ r2_hidden(D_31,k1_funct_2(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_543,plain,(
    '#skF_5'('#skF_9','#skF_10',k1_funct_2('#skF_9','#skF_10'),'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_531,c_26])).

tff(c_24,plain,(
    ! [A_15,B_16,D_31] :
      ( k1_relat_1('#skF_5'(A_15,B_16,k1_funct_2(A_15,B_16),D_31)) = A_15
      | ~ r2_hidden(D_31,k1_funct_2(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_560,plain,
    ( k1_relat_1('#skF_11') = '#skF_9'
    | ~ r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_24])).

tff(c_575,plain,(
    k1_relat_1('#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_560])).

tff(c_340,plain,(
    ! [C_147,B_148] :
      ( r2_hidden('#skF_7'(k1_relat_1(C_147),B_148,C_147),k1_relat_1(C_147))
      | v1_funct_2(C_147,k1_relat_1(C_147),B_148)
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_359,plain,(
    ! [C_147,B_148] :
      ( m1_subset_1('#skF_7'(k1_relat_1(C_147),B_148,C_147),k1_relat_1(C_147))
      | v1_funct_2(C_147,k1_relat_1(C_147),B_148)
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_340,c_14])).

tff(c_590,plain,(
    ! [B_148] :
      ( m1_subset_1('#skF_7'(k1_relat_1('#skF_11'),B_148,'#skF_11'),'#skF_9')
      | v1_funct_2('#skF_11',k1_relat_1('#skF_11'),B_148)
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_359])).

tff(c_616,plain,(
    ! [B_148] :
      ( m1_subset_1('#skF_7'('#skF_9',B_148,'#skF_11'),'#skF_9')
      | v1_funct_2('#skF_11','#skF_9',B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_575,c_575,c_590])).

tff(c_985,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( k3_funct_2(A_209,B_210,C_211,D_212) = k1_funct_1(C_211,D_212)
      | ~ m1_subset_1(D_212,A_209)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_2(C_211,A_209,B_210)
      | ~ v1_funct_1(C_211)
      | v1_xboole_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_995,plain,(
    ! [B_210,C_211,B_148] :
      ( k3_funct_2('#skF_9',B_210,C_211,'#skF_7'('#skF_9',B_148,'#skF_11')) = k1_funct_1(C_211,'#skF_7'('#skF_9',B_148,'#skF_11'))
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_210)))
      | ~ v1_funct_2(C_211,'#skF_9',B_210)
      | ~ v1_funct_1(C_211)
      | v1_xboole_0('#skF_9')
      | v1_funct_2('#skF_11','#skF_9',B_148) ) ),
    inference(resolution,[status(thm)],[c_616,c_985])).

tff(c_1363,plain,(
    ! [B_237,C_238,B_239] :
      ( k3_funct_2('#skF_9',B_237,C_238,'#skF_7'('#skF_9',B_239,'#skF_11')) = k1_funct_1(C_238,'#skF_7'('#skF_9',B_239,'#skF_11'))
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_237)))
      | ~ v1_funct_2(C_238,'#skF_9',B_237)
      | ~ v1_funct_1(C_238)
      | v1_funct_2('#skF_11','#skF_9',B_239) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_995])).

tff(c_1385,plain,(
    ! [B_239] :
      ( k3_funct_2('#skF_9','#skF_10','#skF_11','#skF_7'('#skF_9',B_239,'#skF_11')) = k1_funct_1('#skF_11','#skF_7'('#skF_9',B_239,'#skF_11'))
      | ~ v1_funct_2('#skF_11','#skF_9','#skF_10')
      | ~ v1_funct_1('#skF_11')
      | v1_funct_2('#skF_11','#skF_9',B_239) ) ),
    inference(resolution,[status(thm)],[c_82,c_1363])).

tff(c_1508,plain,(
    ! [B_249] :
      ( k3_funct_2('#skF_9','#skF_10','#skF_11','#skF_7'('#skF_9',B_249,'#skF_11')) = k1_funct_1('#skF_11','#skF_7'('#skF_9',B_249,'#skF_11'))
      | v1_funct_2('#skF_11','#skF_9',B_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_1385])).

tff(c_80,plain,(
    ! [E_65] :
      ( r2_hidden(k3_funct_2('#skF_9','#skF_10','#skF_11',E_65),'#skF_8')
      | ~ m1_subset_1(E_65,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1529,plain,(
    ! [B_251] :
      ( r2_hidden(k1_funct_1('#skF_11','#skF_7'('#skF_9',B_251,'#skF_11')),'#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_9',B_251,'#skF_11'),'#skF_9')
      | v1_funct_2('#skF_11','#skF_9',B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_80])).

tff(c_70,plain,(
    ! [C_52,B_51] :
      ( ~ r2_hidden(k1_funct_1(C_52,'#skF_7'(k1_relat_1(C_52),B_51,C_52)),B_51)
      | v1_funct_2(C_52,k1_relat_1(C_52),B_51)
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_584,plain,(
    ! [B_51] :
      ( ~ r2_hidden(k1_funct_1('#skF_11','#skF_7'('#skF_9',B_51,'#skF_11')),B_51)
      | v1_funct_2('#skF_11',k1_relat_1('#skF_11'),B_51)
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_70])).

tff(c_612,plain,(
    ! [B_51] :
      ( ~ r2_hidden(k1_funct_1('#skF_11','#skF_7'('#skF_9',B_51,'#skF_11')),B_51)
      | v1_funct_2('#skF_11','#skF_9',B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_575,c_584])).

tff(c_1545,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_9','#skF_8','#skF_11'),'#skF_9')
    | v1_funct_2('#skF_11','#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1529,c_612])).

tff(c_1583,plain,(
    ~ m1_subset_1('#skF_7'('#skF_9','#skF_8','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1545])).

tff(c_1599,plain,(
    v1_funct_2('#skF_11','#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_616,c_1583])).

tff(c_634,plain,(
    ! [C_173,B_174] :
      ( r2_hidden('#skF_7'(k1_relat_1(C_173),B_174,C_173),k1_relat_1(C_173))
      | m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_173),B_174)))
      | ~ v1_funct_1(C_173)
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_643,plain,(
    ! [B_174] :
      ( r2_hidden('#skF_7'('#skF_9',B_174,'#skF_11'),k1_relat_1('#skF_11'))
      | m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_11'),B_174)))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_634])).

tff(c_752,plain,(
    ! [B_184] :
      ( r2_hidden('#skF_7'('#skF_9',B_184,'#skF_11'),'#skF_9')
      | m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_184))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_575,c_575,c_643])).

tff(c_60,plain,(
    ! [B_40,C_41,A_39] :
      ( k1_xboole_0 = B_40
      | r2_hidden(C_41,k1_funct_2(A_39,B_40))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_755,plain,(
    ! [B_184] :
      ( k1_xboole_0 = B_184
      | r2_hidden('#skF_11',k1_funct_2('#skF_9',B_184))
      | ~ v1_funct_2('#skF_11','#skF_9',B_184)
      | ~ v1_funct_1('#skF_11')
      | r2_hidden('#skF_7'('#skF_9',B_184,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_752,c_60])).

tff(c_976,plain,(
    ! [B_208] :
      ( k1_xboole_0 = B_208
      | r2_hidden('#skF_11',k1_funct_2('#skF_9',B_208))
      | ~ v1_funct_2('#skF_11','#skF_9',B_208)
      | r2_hidden('#skF_7'('#skF_9',B_208,'#skF_11'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_755])).

tff(c_1046,plain,(
    ! [B_213] :
      ( m1_subset_1('#skF_7'('#skF_9',B_213,'#skF_11'),'#skF_9')
      | k1_xboole_0 = B_213
      | r2_hidden('#skF_11',k1_funct_2('#skF_9',B_213))
      | ~ v1_funct_2('#skF_11','#skF_9',B_213) ) ),
    inference(resolution,[status(thm)],[c_976,c_14])).

tff(c_1060,plain,(
    ! [B_213] :
      ( m1_subset_1('#skF_11',k1_funct_2('#skF_9',B_213))
      | m1_subset_1('#skF_7'('#skF_9',B_213,'#skF_11'),'#skF_9')
      | k1_xboole_0 = B_213
      | ~ v1_funct_2('#skF_11','#skF_9',B_213) ) ),
    inference(resolution,[status(thm)],[c_1046,c_14])).

tff(c_1596,plain,
    ( m1_subset_1('#skF_11',k1_funct_2('#skF_9','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1060,c_1583])).

tff(c_1625,plain,
    ( m1_subset_1('#skF_11',k1_funct_2('#skF_9','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1599,c_1596])).

tff(c_1626,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1625])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1646,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_6])).

tff(c_1648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1646])).

tff(c_1650,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1625])).

tff(c_983,plain,(
    ! [B_208] :
      ( m1_subset_1('#skF_7'('#skF_9',B_208,'#skF_11'),'#skF_9')
      | k1_xboole_0 = B_208
      | r2_hidden('#skF_11',k1_funct_2('#skF_9',B_208))
      | ~ v1_funct_2('#skF_11','#skF_9',B_208) ) ),
    inference(resolution,[status(thm)],[c_976,c_14])).

tff(c_2824,plain,(
    ! [B_335] :
      ( '#skF_5'('#skF_9',B_335,k1_funct_2('#skF_9',B_335),'#skF_11') = '#skF_11'
      | m1_subset_1('#skF_7'('#skF_9',B_335,'#skF_11'),'#skF_9')
      | k1_xboole_0 = B_335
      | ~ v1_funct_2('#skF_11','#skF_9',B_335) ) ),
    inference(resolution,[status(thm)],[c_1046,c_26])).

tff(c_2852,plain,
    ( '#skF_5'('#skF_9','#skF_8',k1_funct_2('#skF_9','#skF_8'),'#skF_11') = '#skF_11'
    | k1_xboole_0 = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_2824,c_1583])).

tff(c_2877,plain,
    ( '#skF_5'('#skF_9','#skF_8',k1_funct_2('#skF_9','#skF_8'),'#skF_11') = '#skF_11'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1599,c_2852])).

tff(c_2878,plain,(
    '#skF_5'('#skF_9','#skF_8',k1_funct_2('#skF_9','#skF_8'),'#skF_11') = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_1650,c_2877])).

tff(c_22,plain,(
    ! [A_15,B_16,D_31] :
      ( r1_tarski(k2_relat_1('#skF_5'(A_15,B_16,k1_funct_2(A_15,B_16),D_31)),B_16)
      | ~ r2_hidden(D_31,k1_funct_2(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2894,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),'#skF_8')
    | ~ r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2878,c_22])).

tff(c_2915,plain,(
    ~ r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_2894])).

tff(c_2945,plain,
    ( m1_subset_1('#skF_7'('#skF_9','#skF_8','#skF_11'),'#skF_9')
    | k1_xboole_0 = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_983,c_2915])).

tff(c_2954,plain,
    ( m1_subset_1('#skF_7'('#skF_9','#skF_8','#skF_11'),'#skF_9')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1599,c_2945])).

tff(c_2956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1650,c_1583,c_2954])).

tff(c_2957,plain,(
    v1_funct_2('#skF_11','#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1545])).

tff(c_2958,plain,(
    m1_subset_1('#skF_7'('#skF_9','#skF_8','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1545])).

tff(c_56,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k3_funct_2(A_35,B_36,C_37,D_38) = k1_funct_1(C_37,D_38)
      | ~ m1_subset_1(D_38,A_35)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(C_37,A_35,B_36)
      | ~ v1_funct_1(C_37)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2960,plain,(
    ! [B_36,C_37] :
      ( k3_funct_2('#skF_9',B_36,C_37,'#skF_7'('#skF_9','#skF_8','#skF_11')) = k1_funct_1(C_37,'#skF_7'('#skF_9','#skF_8','#skF_11'))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_36)))
      | ~ v1_funct_2(C_37,'#skF_9',B_36)
      | ~ v1_funct_1(C_37)
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2958,c_56])).

tff(c_3050,plain,(
    ! [B_346,C_347] :
      ( k3_funct_2('#skF_9',B_346,C_347,'#skF_7'('#skF_9','#skF_8','#skF_11')) = k1_funct_1(C_347,'#skF_7'('#skF_9','#skF_8','#skF_11'))
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_346)))
      | ~ v1_funct_2(C_347,'#skF_9',B_346)
      | ~ v1_funct_1(C_347) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2960])).

tff(c_3083,plain,
    ( k3_funct_2('#skF_9','#skF_10','#skF_11','#skF_7'('#skF_9','#skF_8','#skF_11')) = k1_funct_1('#skF_11','#skF_7'('#skF_9','#skF_8','#skF_11'))
    | ~ v1_funct_2('#skF_11','#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_3050])).

tff(c_3098,plain,(
    k3_funct_2('#skF_9','#skF_10','#skF_11','#skF_7'('#skF_9','#skF_8','#skF_11')) = k1_funct_1('#skF_11','#skF_7'('#skF_9','#skF_8','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_3083])).

tff(c_3119,plain,
    ( r2_hidden(k1_funct_1('#skF_11','#skF_7'('#skF_9','#skF_8','#skF_11')),'#skF_8')
    | ~ m1_subset_1('#skF_7'('#skF_9','#skF_8','#skF_11'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3098,c_80])).

tff(c_3130,plain,(
    r2_hidden(k1_funct_1('#skF_11','#skF_7'('#skF_9','#skF_8','#skF_11')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2958,c_3119])).

tff(c_722,plain,(
    ! [C_180,B_181] :
      ( ~ r2_hidden(k1_funct_1(C_180,'#skF_7'(k1_relat_1(C_180),B_181,C_180)),B_181)
      | m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_180),B_181)))
      | ~ v1_funct_1(C_180)
      | ~ v1_relat_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_725,plain,(
    ! [B_181] :
      ( ~ r2_hidden(k1_funct_1('#skF_11','#skF_7'('#skF_9',B_181,'#skF_11')),B_181)
      | m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_11'),B_181)))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_722])).

tff(c_733,plain,(
    ! [B_181] :
      ( ~ r2_hidden(k1_funct_1('#skF_11','#skF_7'('#skF_9',B_181,'#skF_11')),B_181)
      | m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_181))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_86,c_575,c_725])).

tff(c_3151,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(resolution,[status(thm)],[c_3130,c_733])).

tff(c_3170,plain,
    ( k1_xboole_0 = '#skF_8'
    | r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_8'))
    | ~ v1_funct_2('#skF_11','#skF_9','#skF_8')
    | ~ v1_funct_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_3151,c_60])).

tff(c_3192,plain,
    ( k1_xboole_0 = '#skF_8'
    | r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2957,c_3170])).

tff(c_3225,plain,(
    r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3192])).

tff(c_3237,plain,(
    '#skF_5'('#skF_9','#skF_8',k1_funct_2('#skF_9','#skF_8'),'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_3225,c_26])).

tff(c_3272,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),'#skF_8')
    | ~ r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3237,c_22])).

tff(c_3288,plain,(
    r1_tarski(k2_relat_1('#skF_11'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3225,c_3272])).

tff(c_3290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_3288])).

tff(c_3291,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3192])).

tff(c_3338,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_6])).

tff(c_3340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_3338])).

tff(c_3341,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_3346,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3341,c_6])).

tff(c_3348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3346])).

tff(c_3349,plain,(
    ! [E_69] : ~ m1_subset_1(E_69,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_3366,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_3362,c_3349])).

tff(c_3370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_3366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:40:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.76/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.11  
% 5.76/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.11  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_3
% 5.76/2.11  
% 5.76/2.11  %Foreground sorts:
% 5.76/2.11  
% 5.76/2.11  
% 5.76/2.11  %Background operators:
% 5.76/2.11  
% 5.76/2.11  
% 5.76/2.11  %Foreground operators:
% 5.76/2.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.76/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.76/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.76/2.11  tff('#skF_11', type, '#skF_11': $i).
% 5.76/2.11  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.76/2.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.76/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.11  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.76/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.76/2.11  tff('#skF_10', type, '#skF_10': $i).
% 5.76/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.76/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.76/2.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.76/2.11  tff('#skF_9', type, '#skF_9': $i).
% 5.76/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.76/2.11  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.76/2.11  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.76/2.11  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 5.76/2.11  tff('#skF_8', type, '#skF_8': $i).
% 5.76/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.11  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.76/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.76/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.76/2.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.76/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.76/2.11  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.76/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.76/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.76/2.11  
% 5.95/2.15  tff(f_148, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 5.95/2.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.95/2.15  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.95/2.15  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.95/2.15  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.95/2.15  tff(f_91, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_funct_2)).
% 5.95/2.15  tff(f_66, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 5.95/2.15  tff(f_126, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 5.95/2.15  tff(f_79, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.95/2.15  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.95/2.15  tff(c_90, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.95/2.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.95/2.15  tff(c_3357, plain, (![A_358, B_359]: (m1_subset_1(A_358, B_359) | ~r2_hidden(A_358, B_359))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.95/2.15  tff(c_3362, plain, (![A_360]: (m1_subset_1('#skF_1'(A_360), A_360) | v1_xboole_0(A_360))), inference(resolution, [status(thm)], [c_4, c_3357])).
% 5.95/2.15  tff(c_88, plain, (~v1_xboole_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.95/2.15  tff(c_94, plain, (![E_69]: (r2_hidden(k3_funct_2('#skF_9', '#skF_10', '#skF_11', E_69), '#skF_8') | ~m1_subset_1(E_69, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.95/2.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.95/2.15  tff(c_98, plain, (![E_69]: (~v1_xboole_0('#skF_8') | ~m1_subset_1(E_69, '#skF_9'))), inference(resolution, [status(thm)], [c_94, c_2])).
% 5.95/2.15  tff(c_99, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_98])).
% 5.95/2.15  tff(c_82, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.95/2.15  tff(c_133, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.95/2.15  tff(c_142, plain, (k2_relset_1('#skF_9', '#skF_10', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_82, c_133])).
% 5.95/2.15  tff(c_78, plain, (~r1_tarski(k2_relset_1('#skF_9', '#skF_10', '#skF_11'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.95/2.15  tff(c_143, plain, (~r1_tarski(k2_relat_1('#skF_11'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_78])).
% 5.95/2.15  tff(c_86, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.95/2.15  tff(c_115, plain, (![C_74, A_75, B_76]: (v1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.95/2.15  tff(c_124, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_82, c_115])).
% 5.95/2.15  tff(c_84, plain, (v1_funct_2('#skF_11', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.95/2.15  tff(c_499, plain, (![B_170, C_171, A_172]: (k1_xboole_0=B_170 | r2_hidden(C_171, k1_funct_2(A_172, B_170)) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_170))) | ~v1_funct_2(C_171, A_172, B_170) | ~v1_funct_1(C_171))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.95/2.15  tff(c_522, plain, (k1_xboole_0='#skF_10' | r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_10')) | ~v1_funct_2('#skF_11', '#skF_9', '#skF_10') | ~v1_funct_1('#skF_11')), inference(resolution, [status(thm)], [c_82, c_499])).
% 5.95/2.15  tff(c_530, plain, (k1_xboole_0='#skF_10' | r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_522])).
% 5.95/2.15  tff(c_531, plain, (r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_530])).
% 5.95/2.15  tff(c_26, plain, (![A_15, B_16, D_31]: ('#skF_5'(A_15, B_16, k1_funct_2(A_15, B_16), D_31)=D_31 | ~r2_hidden(D_31, k1_funct_2(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.95/2.15  tff(c_543, plain, ('#skF_5'('#skF_9', '#skF_10', k1_funct_2('#skF_9', '#skF_10'), '#skF_11')='#skF_11'), inference(resolution, [status(thm)], [c_531, c_26])).
% 5.95/2.15  tff(c_24, plain, (![A_15, B_16, D_31]: (k1_relat_1('#skF_5'(A_15, B_16, k1_funct_2(A_15, B_16), D_31))=A_15 | ~r2_hidden(D_31, k1_funct_2(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.95/2.15  tff(c_560, plain, (k1_relat_1('#skF_11')='#skF_9' | ~r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_543, c_24])).
% 5.95/2.15  tff(c_575, plain, (k1_relat_1('#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_531, c_560])).
% 5.95/2.15  tff(c_340, plain, (![C_147, B_148]: (r2_hidden('#skF_7'(k1_relat_1(C_147), B_148, C_147), k1_relat_1(C_147)) | v1_funct_2(C_147, k1_relat_1(C_147), B_148) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.95/2.15  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.95/2.15  tff(c_359, plain, (![C_147, B_148]: (m1_subset_1('#skF_7'(k1_relat_1(C_147), B_148, C_147), k1_relat_1(C_147)) | v1_funct_2(C_147, k1_relat_1(C_147), B_148) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_340, c_14])).
% 5.95/2.15  tff(c_590, plain, (![B_148]: (m1_subset_1('#skF_7'(k1_relat_1('#skF_11'), B_148, '#skF_11'), '#skF_9') | v1_funct_2('#skF_11', k1_relat_1('#skF_11'), B_148) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_575, c_359])).
% 5.95/2.15  tff(c_616, plain, (![B_148]: (m1_subset_1('#skF_7'('#skF_9', B_148, '#skF_11'), '#skF_9') | v1_funct_2('#skF_11', '#skF_9', B_148))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_575, c_575, c_590])).
% 5.95/2.15  tff(c_985, plain, (![A_209, B_210, C_211, D_212]: (k3_funct_2(A_209, B_210, C_211, D_212)=k1_funct_1(C_211, D_212) | ~m1_subset_1(D_212, A_209) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_2(C_211, A_209, B_210) | ~v1_funct_1(C_211) | v1_xboole_0(A_209))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.95/2.15  tff(c_995, plain, (![B_210, C_211, B_148]: (k3_funct_2('#skF_9', B_210, C_211, '#skF_7'('#skF_9', B_148, '#skF_11'))=k1_funct_1(C_211, '#skF_7'('#skF_9', B_148, '#skF_11')) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_210))) | ~v1_funct_2(C_211, '#skF_9', B_210) | ~v1_funct_1(C_211) | v1_xboole_0('#skF_9') | v1_funct_2('#skF_11', '#skF_9', B_148))), inference(resolution, [status(thm)], [c_616, c_985])).
% 5.95/2.15  tff(c_1363, plain, (![B_237, C_238, B_239]: (k3_funct_2('#skF_9', B_237, C_238, '#skF_7'('#skF_9', B_239, '#skF_11'))=k1_funct_1(C_238, '#skF_7'('#skF_9', B_239, '#skF_11')) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_237))) | ~v1_funct_2(C_238, '#skF_9', B_237) | ~v1_funct_1(C_238) | v1_funct_2('#skF_11', '#skF_9', B_239))), inference(negUnitSimplification, [status(thm)], [c_90, c_995])).
% 5.95/2.15  tff(c_1385, plain, (![B_239]: (k3_funct_2('#skF_9', '#skF_10', '#skF_11', '#skF_7'('#skF_9', B_239, '#skF_11'))=k1_funct_1('#skF_11', '#skF_7'('#skF_9', B_239, '#skF_11')) | ~v1_funct_2('#skF_11', '#skF_9', '#skF_10') | ~v1_funct_1('#skF_11') | v1_funct_2('#skF_11', '#skF_9', B_239))), inference(resolution, [status(thm)], [c_82, c_1363])).
% 5.95/2.15  tff(c_1508, plain, (![B_249]: (k3_funct_2('#skF_9', '#skF_10', '#skF_11', '#skF_7'('#skF_9', B_249, '#skF_11'))=k1_funct_1('#skF_11', '#skF_7'('#skF_9', B_249, '#skF_11')) | v1_funct_2('#skF_11', '#skF_9', B_249))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_1385])).
% 5.95/2.15  tff(c_80, plain, (![E_65]: (r2_hidden(k3_funct_2('#skF_9', '#skF_10', '#skF_11', E_65), '#skF_8') | ~m1_subset_1(E_65, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.95/2.15  tff(c_1529, plain, (![B_251]: (r2_hidden(k1_funct_1('#skF_11', '#skF_7'('#skF_9', B_251, '#skF_11')), '#skF_8') | ~m1_subset_1('#skF_7'('#skF_9', B_251, '#skF_11'), '#skF_9') | v1_funct_2('#skF_11', '#skF_9', B_251))), inference(superposition, [status(thm), theory('equality')], [c_1508, c_80])).
% 5.95/2.15  tff(c_70, plain, (![C_52, B_51]: (~r2_hidden(k1_funct_1(C_52, '#skF_7'(k1_relat_1(C_52), B_51, C_52)), B_51) | v1_funct_2(C_52, k1_relat_1(C_52), B_51) | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.95/2.15  tff(c_584, plain, (![B_51]: (~r2_hidden(k1_funct_1('#skF_11', '#skF_7'('#skF_9', B_51, '#skF_11')), B_51) | v1_funct_2('#skF_11', k1_relat_1('#skF_11'), B_51) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_575, c_70])).
% 5.95/2.15  tff(c_612, plain, (![B_51]: (~r2_hidden(k1_funct_1('#skF_11', '#skF_7'('#skF_9', B_51, '#skF_11')), B_51) | v1_funct_2('#skF_11', '#skF_9', B_51))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_575, c_584])).
% 5.95/2.15  tff(c_1545, plain, (~m1_subset_1('#skF_7'('#skF_9', '#skF_8', '#skF_11'), '#skF_9') | v1_funct_2('#skF_11', '#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1529, c_612])).
% 5.95/2.15  tff(c_1583, plain, (~m1_subset_1('#skF_7'('#skF_9', '#skF_8', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_1545])).
% 5.95/2.15  tff(c_1599, plain, (v1_funct_2('#skF_11', '#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_616, c_1583])).
% 5.95/2.15  tff(c_634, plain, (![C_173, B_174]: (r2_hidden('#skF_7'(k1_relat_1(C_173), B_174, C_173), k1_relat_1(C_173)) | m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_173), B_174))) | ~v1_funct_1(C_173) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.95/2.15  tff(c_643, plain, (![B_174]: (r2_hidden('#skF_7'('#skF_9', B_174, '#skF_11'), k1_relat_1('#skF_11')) | m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_11'), B_174))) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_575, c_634])).
% 5.95/2.15  tff(c_752, plain, (![B_184]: (r2_hidden('#skF_7'('#skF_9', B_184, '#skF_11'), '#skF_9') | m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_184))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_575, c_575, c_643])).
% 5.95/2.15  tff(c_60, plain, (![B_40, C_41, A_39]: (k1_xboole_0=B_40 | r2_hidden(C_41, k1_funct_2(A_39, B_40)) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(C_41, A_39, B_40) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.95/2.15  tff(c_755, plain, (![B_184]: (k1_xboole_0=B_184 | r2_hidden('#skF_11', k1_funct_2('#skF_9', B_184)) | ~v1_funct_2('#skF_11', '#skF_9', B_184) | ~v1_funct_1('#skF_11') | r2_hidden('#skF_7'('#skF_9', B_184, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_752, c_60])).
% 5.95/2.15  tff(c_976, plain, (![B_208]: (k1_xboole_0=B_208 | r2_hidden('#skF_11', k1_funct_2('#skF_9', B_208)) | ~v1_funct_2('#skF_11', '#skF_9', B_208) | r2_hidden('#skF_7'('#skF_9', B_208, '#skF_11'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_755])).
% 5.95/2.15  tff(c_1046, plain, (![B_213]: (m1_subset_1('#skF_7'('#skF_9', B_213, '#skF_11'), '#skF_9') | k1_xboole_0=B_213 | r2_hidden('#skF_11', k1_funct_2('#skF_9', B_213)) | ~v1_funct_2('#skF_11', '#skF_9', B_213))), inference(resolution, [status(thm)], [c_976, c_14])).
% 5.95/2.15  tff(c_1060, plain, (![B_213]: (m1_subset_1('#skF_11', k1_funct_2('#skF_9', B_213)) | m1_subset_1('#skF_7'('#skF_9', B_213, '#skF_11'), '#skF_9') | k1_xboole_0=B_213 | ~v1_funct_2('#skF_11', '#skF_9', B_213))), inference(resolution, [status(thm)], [c_1046, c_14])).
% 5.95/2.15  tff(c_1596, plain, (m1_subset_1('#skF_11', k1_funct_2('#skF_9', '#skF_8')) | k1_xboole_0='#skF_8' | ~v1_funct_2('#skF_11', '#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1060, c_1583])).
% 5.95/2.15  tff(c_1625, plain, (m1_subset_1('#skF_11', k1_funct_2('#skF_9', '#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1599, c_1596])).
% 5.95/2.15  tff(c_1626, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_1625])).
% 5.95/2.15  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.95/2.15  tff(c_1646, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1626, c_6])).
% 5.95/2.15  tff(c_1648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_1646])).
% 5.95/2.15  tff(c_1650, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_1625])).
% 5.95/2.15  tff(c_983, plain, (![B_208]: (m1_subset_1('#skF_7'('#skF_9', B_208, '#skF_11'), '#skF_9') | k1_xboole_0=B_208 | r2_hidden('#skF_11', k1_funct_2('#skF_9', B_208)) | ~v1_funct_2('#skF_11', '#skF_9', B_208))), inference(resolution, [status(thm)], [c_976, c_14])).
% 5.95/2.15  tff(c_2824, plain, (![B_335]: ('#skF_5'('#skF_9', B_335, k1_funct_2('#skF_9', B_335), '#skF_11')='#skF_11' | m1_subset_1('#skF_7'('#skF_9', B_335, '#skF_11'), '#skF_9') | k1_xboole_0=B_335 | ~v1_funct_2('#skF_11', '#skF_9', B_335))), inference(resolution, [status(thm)], [c_1046, c_26])).
% 5.95/2.15  tff(c_2852, plain, ('#skF_5'('#skF_9', '#skF_8', k1_funct_2('#skF_9', '#skF_8'), '#skF_11')='#skF_11' | k1_xboole_0='#skF_8' | ~v1_funct_2('#skF_11', '#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_2824, c_1583])).
% 5.95/2.15  tff(c_2877, plain, ('#skF_5'('#skF_9', '#skF_8', k1_funct_2('#skF_9', '#skF_8'), '#skF_11')='#skF_11' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1599, c_2852])).
% 5.95/2.15  tff(c_2878, plain, ('#skF_5'('#skF_9', '#skF_8', k1_funct_2('#skF_9', '#skF_8'), '#skF_11')='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_1650, c_2877])).
% 5.95/2.15  tff(c_22, plain, (![A_15, B_16, D_31]: (r1_tarski(k2_relat_1('#skF_5'(A_15, B_16, k1_funct_2(A_15, B_16), D_31)), B_16) | ~r2_hidden(D_31, k1_funct_2(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.95/2.15  tff(c_2894, plain, (r1_tarski(k2_relat_1('#skF_11'), '#skF_8') | ~r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2878, c_22])).
% 5.95/2.15  tff(c_2915, plain, (~r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_143, c_2894])).
% 5.95/2.15  tff(c_2945, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_8', '#skF_11'), '#skF_9') | k1_xboole_0='#skF_8' | ~v1_funct_2('#skF_11', '#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_983, c_2915])).
% 5.95/2.15  tff(c_2954, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_8', '#skF_11'), '#skF_9') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1599, c_2945])).
% 5.95/2.15  tff(c_2956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1650, c_1583, c_2954])).
% 5.95/2.15  tff(c_2957, plain, (v1_funct_2('#skF_11', '#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_1545])).
% 5.95/2.15  tff(c_2958, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_8', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_1545])).
% 5.95/2.15  tff(c_56, plain, (![A_35, B_36, C_37, D_38]: (k3_funct_2(A_35, B_36, C_37, D_38)=k1_funct_1(C_37, D_38) | ~m1_subset_1(D_38, A_35) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(C_37, A_35, B_36) | ~v1_funct_1(C_37) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.95/2.15  tff(c_2960, plain, (![B_36, C_37]: (k3_funct_2('#skF_9', B_36, C_37, '#skF_7'('#skF_9', '#skF_8', '#skF_11'))=k1_funct_1(C_37, '#skF_7'('#skF_9', '#skF_8', '#skF_11')) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_36))) | ~v1_funct_2(C_37, '#skF_9', B_36) | ~v1_funct_1(C_37) | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_2958, c_56])).
% 5.95/2.15  tff(c_3050, plain, (![B_346, C_347]: (k3_funct_2('#skF_9', B_346, C_347, '#skF_7'('#skF_9', '#skF_8', '#skF_11'))=k1_funct_1(C_347, '#skF_7'('#skF_9', '#skF_8', '#skF_11')) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_346))) | ~v1_funct_2(C_347, '#skF_9', B_346) | ~v1_funct_1(C_347))), inference(negUnitSimplification, [status(thm)], [c_90, c_2960])).
% 5.95/2.15  tff(c_3083, plain, (k3_funct_2('#skF_9', '#skF_10', '#skF_11', '#skF_7'('#skF_9', '#skF_8', '#skF_11'))=k1_funct_1('#skF_11', '#skF_7'('#skF_9', '#skF_8', '#skF_11')) | ~v1_funct_2('#skF_11', '#skF_9', '#skF_10') | ~v1_funct_1('#skF_11')), inference(resolution, [status(thm)], [c_82, c_3050])).
% 5.95/2.15  tff(c_3098, plain, (k3_funct_2('#skF_9', '#skF_10', '#skF_11', '#skF_7'('#skF_9', '#skF_8', '#skF_11'))=k1_funct_1('#skF_11', '#skF_7'('#skF_9', '#skF_8', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_3083])).
% 5.95/2.15  tff(c_3119, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_7'('#skF_9', '#skF_8', '#skF_11')), '#skF_8') | ~m1_subset_1('#skF_7'('#skF_9', '#skF_8', '#skF_11'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3098, c_80])).
% 5.95/2.15  tff(c_3130, plain, (r2_hidden(k1_funct_1('#skF_11', '#skF_7'('#skF_9', '#skF_8', '#skF_11')), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2958, c_3119])).
% 5.95/2.15  tff(c_722, plain, (![C_180, B_181]: (~r2_hidden(k1_funct_1(C_180, '#skF_7'(k1_relat_1(C_180), B_181, C_180)), B_181) | m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_180), B_181))) | ~v1_funct_1(C_180) | ~v1_relat_1(C_180))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.95/2.15  tff(c_725, plain, (![B_181]: (~r2_hidden(k1_funct_1('#skF_11', '#skF_7'('#skF_9', B_181, '#skF_11')), B_181) | m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_11'), B_181))) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_575, c_722])).
% 5.95/2.15  tff(c_733, plain, (![B_181]: (~r2_hidden(k1_funct_1('#skF_11', '#skF_7'('#skF_9', B_181, '#skF_11')), B_181) | m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_181))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_86, c_575, c_725])).
% 5.95/2.15  tff(c_3151, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(resolution, [status(thm)], [c_3130, c_733])).
% 5.95/2.15  tff(c_3170, plain, (k1_xboole_0='#skF_8' | r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_8')) | ~v1_funct_2('#skF_11', '#skF_9', '#skF_8') | ~v1_funct_1('#skF_11')), inference(resolution, [status(thm)], [c_3151, c_60])).
% 5.95/2.15  tff(c_3192, plain, (k1_xboole_0='#skF_8' | r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2957, c_3170])).
% 5.95/2.15  tff(c_3225, plain, (r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_3192])).
% 5.95/2.15  tff(c_3237, plain, ('#skF_5'('#skF_9', '#skF_8', k1_funct_2('#skF_9', '#skF_8'), '#skF_11')='#skF_11'), inference(resolution, [status(thm)], [c_3225, c_26])).
% 5.95/2.15  tff(c_3272, plain, (r1_tarski(k2_relat_1('#skF_11'), '#skF_8') | ~r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3237, c_22])).
% 5.95/2.15  tff(c_3288, plain, (r1_tarski(k2_relat_1('#skF_11'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3225, c_3272])).
% 5.95/2.15  tff(c_3290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_3288])).
% 5.95/2.15  tff(c_3291, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_3192])).
% 5.95/2.15  tff(c_3338, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_6])).
% 5.95/2.15  tff(c_3340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_3338])).
% 5.95/2.15  tff(c_3341, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_530])).
% 5.95/2.15  tff(c_3346, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3341, c_6])).
% 5.95/2.15  tff(c_3348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3346])).
% 5.95/2.15  tff(c_3349, plain, (![E_69]: (~m1_subset_1(E_69, '#skF_9'))), inference(splitRight, [status(thm)], [c_98])).
% 5.95/2.15  tff(c_3366, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_3362, c_3349])).
% 5.95/2.15  tff(c_3370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_3366])).
% 5.95/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.95/2.15  
% 5.95/2.15  Inference rules
% 5.95/2.15  ----------------------
% 5.95/2.15  #Ref     : 0
% 5.95/2.15  #Sup     : 785
% 5.95/2.15  #Fact    : 0
% 5.95/2.15  #Define  : 0
% 5.95/2.15  #Split   : 18
% 5.95/2.15  #Chain   : 0
% 5.95/2.15  #Close   : 0
% 5.95/2.15  
% 5.95/2.15  Ordering : KBO
% 5.95/2.15  
% 5.95/2.15  Simplification rules
% 5.95/2.15  ----------------------
% 5.95/2.15  #Subsume      : 82
% 5.95/2.15  #Demod        : 355
% 5.95/2.15  #Tautology    : 126
% 5.95/2.15  #SimpNegUnit  : 25
% 5.95/2.15  #BackRed      : 52
% 5.95/2.15  
% 5.95/2.15  #Partial instantiations: 0
% 5.95/2.15  #Strategies tried      : 1
% 5.95/2.15  
% 5.95/2.15  Timing (in seconds)
% 5.95/2.15  ----------------------
% 5.95/2.15  Preprocessing        : 0.35
% 5.95/2.15  Parsing              : 0.17
% 5.95/2.15  CNF conversion       : 0.03
% 5.95/2.15  Main loop            : 0.98
% 5.95/2.15  Inferencing          : 0.33
% 5.95/2.15  Reduction            : 0.29
% 5.95/2.16  Demodulation         : 0.20
% 5.95/2.16  BG Simplification    : 0.06
% 5.95/2.16  Subsumption          : 0.20
% 5.95/2.16  Abstraction          : 0.06
% 5.95/2.16  MUC search           : 0.00
% 5.95/2.16  Cooper               : 0.00
% 5.95/2.16  Total                : 1.40
% 5.95/2.16  Index Insertion      : 0.00
% 5.95/2.16  Index Deletion       : 0.00
% 5.95/2.16  Index Matching       : 0.00
% 5.95/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
