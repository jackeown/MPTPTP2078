%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:15 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 131 expanded)
%              Number of leaves         :   45 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  136 ( 241 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_73,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_117,plain,(
    ! [A_59,B_60] :
      ( k9_relat_1(A_59,k1_tarski(B_60)) = k11_relat_1(A_59,B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_82,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_22])).

tff(c_89,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_86])).

tff(c_94,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(k7_relat_1(B_54,A_55)) = k9_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_103,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_94])).

tff(c_107,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_103])).

tff(c_123,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_107])).

tff(c_132,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_123])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,k1_relat_1(B_16))
      | k11_relat_1(B_16,A_15) = k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_164,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_168,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_164])).

tff(c_194,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k2_relset_1(A_79,B_80,C_81),k1_zfmisc_1(B_80))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_217,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_194])).

tff(c_224,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_217])).

tff(c_231,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(k1_funct_1(B_84,A_85),k2_relat_1(B_84))
      | ~ r2_hidden(A_85,k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_376,plain,(
    ! [B_128,A_129,A_130] :
      ( r2_hidden(k1_funct_1(B_128,A_129),A_130)
      | ~ m1_subset_1(k2_relat_1(B_128),k1_zfmisc_1(A_130))
      | ~ r2_hidden(A_129,k1_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_231,c_12])).

tff(c_378,plain,(
    ! [A_129] :
      ( r2_hidden(k1_funct_1('#skF_4',A_129),'#skF_3')
      | ~ r2_hidden(A_129,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_224,c_376])).

tff(c_384,plain,(
    ! [A_131] :
      ( r2_hidden(k1_funct_1('#skF_4',A_131),'#skF_3')
      | ~ r2_hidden(A_131,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_48,c_378])).

tff(c_40,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_395,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_384,c_40])).

tff(c_398,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_395])).

tff(c_401,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_132,c_398])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_242,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( r2_hidden(k1_funct_1(D_86,C_87),k2_relset_1(A_88,B_89,D_86))
      | k1_xboole_0 = B_89
      | ~ r2_hidden(C_87,A_88)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(D_86,A_88,B_89)
      | ~ v1_funct_1(D_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_250,plain,(
    ! [C_87] :
      ( r2_hidden(k1_funct_1('#skF_4',C_87),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_87,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_242])).

tff(c_254,plain,(
    ! [C_87] :
      ( r2_hidden(k1_funct_1('#skF_4',C_87),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_87,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_250])).

tff(c_256,plain,(
    ! [C_90] :
      ( r2_hidden(k1_funct_1('#skF_4',C_90),k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_90,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_254])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_263,plain,(
    ! [C_90] :
      ( ~ r1_tarski(k2_relat_1('#skF_4'),k1_funct_1('#skF_4',C_90))
      | ~ r2_hidden(C_90,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_256,c_26])).

tff(c_404,plain,(
    ! [C_90] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_4',C_90))
      | ~ r2_hidden(C_90,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_263])).

tff(c_430,plain,(
    ! [C_132] : ~ r2_hidden(C_132,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_404])).

tff(c_440,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_430])).

tff(c_10,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_457,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_10])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:03:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.42  
% 2.53/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.53/1.43  
% 2.53/1.43  %Foreground sorts:
% 2.53/1.43  
% 2.53/1.43  
% 2.53/1.43  %Background operators:
% 2.53/1.43  
% 2.53/1.43  
% 2.53/1.43  %Foreground operators:
% 2.53/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.53/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.53/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.53/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.53/1.43  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.53/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.53/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.53/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.53/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.53/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.43  
% 2.53/1.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.53/1.44  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.53/1.44  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.53/1.44  tff(f_125, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.53/1.44  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.53/1.44  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.53/1.44  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.53/1.44  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.53/1.44  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.53/1.44  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.53/1.44  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.53/1.44  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.53/1.44  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.53/1.44  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.53/1.44  tff(f_113, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.53/1.44  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.53/1.44  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.53/1.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.53/1.44  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.44  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.53/1.44  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.53/1.44  tff(c_73, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.44  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_73])).
% 2.53/1.44  tff(c_117, plain, (![A_59, B_60]: (k9_relat_1(A_59, k1_tarski(B_60))=k11_relat_1(A_59, B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.44  tff(c_78, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.44  tff(c_82, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_78])).
% 2.53/1.44  tff(c_22, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.53/1.44  tff(c_86, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_22])).
% 2.53/1.44  tff(c_89, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_86])).
% 2.53/1.44  tff(c_94, plain, (![B_54, A_55]: (k2_relat_1(k7_relat_1(B_54, A_55))=k9_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.53/1.44  tff(c_103, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_89, c_94])).
% 2.53/1.44  tff(c_107, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_103])).
% 2.53/1.44  tff(c_123, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_117, c_107])).
% 2.53/1.44  tff(c_132, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_123])).
% 2.53/1.44  tff(c_18, plain, (![A_15, B_16]: (r2_hidden(A_15, k1_relat_1(B_16)) | k11_relat_1(B_16, A_15)=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.44  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.53/1.44  tff(c_164, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.53/1.44  tff(c_168, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_164])).
% 2.53/1.44  tff(c_194, plain, (![A_79, B_80, C_81]: (m1_subset_1(k2_relset_1(A_79, B_80, C_81), k1_zfmisc_1(B_80)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.44  tff(c_217, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_168, c_194])).
% 2.53/1.44  tff(c_224, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_217])).
% 2.53/1.44  tff(c_231, plain, (![B_84, A_85]: (r2_hidden(k1_funct_1(B_84, A_85), k2_relat_1(B_84)) | ~r2_hidden(A_85, k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.44  tff(c_12, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.53/1.44  tff(c_376, plain, (![B_128, A_129, A_130]: (r2_hidden(k1_funct_1(B_128, A_129), A_130) | ~m1_subset_1(k2_relat_1(B_128), k1_zfmisc_1(A_130)) | ~r2_hidden(A_129, k1_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_231, c_12])).
% 2.53/1.44  tff(c_378, plain, (![A_129]: (r2_hidden(k1_funct_1('#skF_4', A_129), '#skF_3') | ~r2_hidden(A_129, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_224, c_376])).
% 2.53/1.44  tff(c_384, plain, (![A_131]: (r2_hidden(k1_funct_1('#skF_4', A_131), '#skF_3') | ~r2_hidden(A_131, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_48, c_378])).
% 2.53/1.44  tff(c_40, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.53/1.44  tff(c_395, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_384, c_40])).
% 2.53/1.44  tff(c_398, plain, (k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_395])).
% 2.53/1.44  tff(c_401, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77, c_132, c_398])).
% 2.53/1.44  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.53/1.44  tff(c_46, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.53/1.44  tff(c_242, plain, (![D_86, C_87, A_88, B_89]: (r2_hidden(k1_funct_1(D_86, C_87), k2_relset_1(A_88, B_89, D_86)) | k1_xboole_0=B_89 | ~r2_hidden(C_87, A_88) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(D_86, A_88, B_89) | ~v1_funct_1(D_86))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.44  tff(c_250, plain, (![C_87]: (r2_hidden(k1_funct_1('#skF_4', C_87), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_87, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_242])).
% 2.53/1.44  tff(c_254, plain, (![C_87]: (r2_hidden(k1_funct_1('#skF_4', C_87), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_87, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_250])).
% 2.53/1.44  tff(c_256, plain, (![C_90]: (r2_hidden(k1_funct_1('#skF_4', C_90), k2_relat_1('#skF_4')) | ~r2_hidden(C_90, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_254])).
% 2.53/1.44  tff(c_26, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.53/1.44  tff(c_263, plain, (![C_90]: (~r1_tarski(k2_relat_1('#skF_4'), k1_funct_1('#skF_4', C_90)) | ~r2_hidden(C_90, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_256, c_26])).
% 2.53/1.44  tff(c_404, plain, (![C_90]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_4', C_90)) | ~r2_hidden(C_90, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_263])).
% 2.53/1.44  tff(c_430, plain, (![C_132]: (~r2_hidden(C_132, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_404])).
% 2.53/1.44  tff(c_440, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_430])).
% 2.53/1.44  tff(c_10, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.44  tff(c_457, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_440, c_10])).
% 2.53/1.44  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_457])).
% 2.53/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.44  
% 2.53/1.44  Inference rules
% 2.53/1.44  ----------------------
% 2.53/1.44  #Ref     : 0
% 2.53/1.44  #Sup     : 88
% 2.53/1.44  #Fact    : 0
% 2.53/1.44  #Define  : 0
% 2.53/1.44  #Split   : 3
% 2.53/1.44  #Chain   : 0
% 2.53/1.44  #Close   : 0
% 2.53/1.44  
% 2.53/1.44  Ordering : KBO
% 2.53/1.44  
% 2.53/1.44  Simplification rules
% 2.53/1.44  ----------------------
% 2.53/1.44  #Subsume      : 9
% 2.53/1.44  #Demod        : 41
% 2.53/1.44  #Tautology    : 20
% 2.53/1.44  #SimpNegUnit  : 1
% 2.53/1.44  #BackRed      : 19
% 2.53/1.44  
% 2.53/1.44  #Partial instantiations: 0
% 2.53/1.44  #Strategies tried      : 1
% 2.53/1.44  
% 2.53/1.45  Timing (in seconds)
% 2.53/1.45  ----------------------
% 2.53/1.45  Preprocessing        : 0.32
% 2.53/1.45  Parsing              : 0.17
% 2.53/1.45  CNF conversion       : 0.02
% 2.53/1.45  Main loop            : 0.29
% 2.53/1.45  Inferencing          : 0.11
% 2.53/1.45  Reduction            : 0.08
% 2.53/1.45  Demodulation         : 0.05
% 2.53/1.45  BG Simplification    : 0.02
% 2.53/1.45  Subsumption          : 0.06
% 2.53/1.45  Abstraction          : 0.01
% 2.53/1.45  MUC search           : 0.00
% 2.53/1.45  Cooper               : 0.00
% 2.53/1.45  Total                : 0.65
% 2.53/1.45  Index Insertion      : 0.00
% 2.53/1.45  Index Deletion       : 0.00
% 2.53/1.45  Index Matching       : 0.00
% 2.53/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
