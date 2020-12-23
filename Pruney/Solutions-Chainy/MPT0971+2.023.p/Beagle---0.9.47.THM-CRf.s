%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:32 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 130 expanded)
%              Number of leaves         :   46 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  135 ( 257 expanded)
%              Number of equality atoms :   33 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_26,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_111,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_117,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_111])).

tff(c_121,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_117])).

tff(c_74,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_30,plain,(
    ! [A_26,C_62] :
      ( k1_funct_1(A_26,'#skF_4'(A_26,k2_relat_1(A_26),C_62)) = C_62
      | ~ r2_hidden(C_62,k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_209,plain,(
    ! [C_119,B_120,A_121] :
      ( v5_relat_1(C_119,B_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_223,plain,(
    v5_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_209])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k2_relat_1(B_23),A_22)
      | ~ v5_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_287,plain,(
    ! [A_142,B_143,C_144] :
      ( k2_relset_1(A_142,B_143,C_144) = k2_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_301,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_287])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_258,plain,(
    ! [C_127,A_128,B_129] :
      ( r2_hidden(C_127,A_128)
      | ~ r2_hidden(C_127,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_264,plain,(
    ! [A_136] :
      ( r2_hidden('#skF_7',A_136)
      | ~ m1_subset_1(k2_relset_1('#skF_5','#skF_6','#skF_8'),k1_zfmisc_1(A_136)) ) ),
    inference(resolution,[status(thm)],[c_68,c_258])).

tff(c_269,plain,(
    ! [B_18] :
      ( r2_hidden('#skF_7',B_18)
      | ~ r1_tarski(k2_relset_1('#skF_5','#skF_6','#skF_8'),B_18) ) ),
    inference(resolution,[status(thm)],[c_18,c_264])).

tff(c_321,plain,(
    ! [B_145] :
      ( r2_hidden('#skF_7',B_145)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_269])).

tff(c_325,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_7',A_22)
      | ~ v5_relat_1('#skF_8',A_22)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_24,c_321])).

tff(c_329,plain,(
    ! [A_146] :
      ( r2_hidden('#skF_7',A_146)
      | ~ v5_relat_1('#skF_8',A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_325])).

tff(c_333,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_223,c_329])).

tff(c_122,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k1_tarski(A_96),k1_zfmisc_1(B_97))
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k1_tarski(A_100),B_101)
      | ~ r2_hidden(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_122,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_104,B_105] :
      ( k2_xboole_0(k1_tarski(A_104),B_105) = B_105
      | ~ r2_hidden(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),B_10) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_161,plain,(
    ! [B_105,A_104] :
      ( k1_xboole_0 != B_105
      | ~ r2_hidden(A_104,B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_10])).

tff(c_342,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_333,c_161])).

tff(c_72,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_344,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_358,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_344])).

tff(c_668,plain,(
    ! [B_230,A_231,C_232] :
      ( k1_xboole_0 = B_230
      | k1_relset_1(A_231,B_230,C_232) = A_231
      | ~ v1_funct_2(C_232,A_231,B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_679,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_668])).

tff(c_684,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_358,c_679])).

tff(c_685,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_684])).

tff(c_32,plain,(
    ! [A_26,C_62] :
      ( r2_hidden('#skF_4'(A_26,k2_relat_1(A_26),C_62),k1_relat_1(A_26))
      | ~ r2_hidden(C_62,k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_691,plain,(
    ! [C_62] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_62),'#skF_5')
      | ~ r2_hidden(C_62,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_32])).

tff(c_729,plain,(
    ! [C_236] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_236),'#skF_5')
      | ~ r2_hidden(C_236,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_74,c_691])).

tff(c_66,plain,(
    ! [E_79] :
      ( k1_funct_1('#skF_8',E_79) != '#skF_7'
      | ~ r2_hidden(E_79,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_744,plain,(
    ! [C_237] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_237)) != '#skF_7'
      | ~ r2_hidden(C_237,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_729,c_66])).

tff(c_748,plain,(
    ! [C_62] :
      ( C_62 != '#skF_7'
      | ~ r2_hidden(C_62,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_62,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_744])).

tff(c_751,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_74,c_748])).

tff(c_306,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_68])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_751,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:21:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.55  
% 3.47/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 3.47/1.56  
% 3.47/1.56  %Foreground sorts:
% 3.47/1.56  
% 3.47/1.56  
% 3.47/1.56  %Background operators:
% 3.47/1.56  
% 3.47/1.56  
% 3.47/1.56  %Foreground operators:
% 3.47/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.47/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.47/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.47/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.47/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.47/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.47/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.47/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.47/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.47/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.47/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.47/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.47/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.47/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.56  
% 3.47/1.57  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.47/1.57  tff(f_131, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 3.47/1.57  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.47/1.57  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.47/1.57  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.47/1.57  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.47/1.57  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.47/1.57  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.47/1.57  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.47/1.57  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.47/1.57  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.47/1.57  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.47/1.57  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.47/1.57  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.47/1.57  tff(c_26, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.47/1.57  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.47/1.57  tff(c_111, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.47/1.57  tff(c_117, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_111])).
% 3.47/1.57  tff(c_121, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_117])).
% 3.47/1.57  tff(c_74, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.47/1.57  tff(c_30, plain, (![A_26, C_62]: (k1_funct_1(A_26, '#skF_4'(A_26, k2_relat_1(A_26), C_62))=C_62 | ~r2_hidden(C_62, k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.47/1.57  tff(c_209, plain, (![C_119, B_120, A_121]: (v5_relat_1(C_119, B_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.47/1.57  tff(c_223, plain, (v5_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_209])).
% 3.47/1.57  tff(c_24, plain, (![B_23, A_22]: (r1_tarski(k2_relat_1(B_23), A_22) | ~v5_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.57  tff(c_287, plain, (![A_142, B_143, C_144]: (k2_relset_1(A_142, B_143, C_144)=k2_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.47/1.57  tff(c_301, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_287])).
% 3.47/1.57  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.47/1.57  tff(c_68, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.47/1.57  tff(c_258, plain, (![C_127, A_128, B_129]: (r2_hidden(C_127, A_128) | ~r2_hidden(C_127, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.57  tff(c_264, plain, (![A_136]: (r2_hidden('#skF_7', A_136) | ~m1_subset_1(k2_relset_1('#skF_5', '#skF_6', '#skF_8'), k1_zfmisc_1(A_136)))), inference(resolution, [status(thm)], [c_68, c_258])).
% 3.47/1.57  tff(c_269, plain, (![B_18]: (r2_hidden('#skF_7', B_18) | ~r1_tarski(k2_relset_1('#skF_5', '#skF_6', '#skF_8'), B_18))), inference(resolution, [status(thm)], [c_18, c_264])).
% 3.47/1.57  tff(c_321, plain, (![B_145]: (r2_hidden('#skF_7', B_145) | ~r1_tarski(k2_relat_1('#skF_8'), B_145))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_269])).
% 3.47/1.57  tff(c_325, plain, (![A_22]: (r2_hidden('#skF_7', A_22) | ~v5_relat_1('#skF_8', A_22) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_24, c_321])).
% 3.47/1.57  tff(c_329, plain, (![A_146]: (r2_hidden('#skF_7', A_146) | ~v5_relat_1('#skF_8', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_325])).
% 3.47/1.57  tff(c_333, plain, (r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_223, c_329])).
% 3.47/1.57  tff(c_122, plain, (![A_96, B_97]: (m1_subset_1(k1_tarski(A_96), k1_zfmisc_1(B_97)) | ~r2_hidden(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.47/1.57  tff(c_16, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.47/1.57  tff(c_138, plain, (![A_100, B_101]: (r1_tarski(k1_tarski(A_100), B_101) | ~r2_hidden(A_100, B_101))), inference(resolution, [status(thm)], [c_122, c_16])).
% 3.47/1.57  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.47/1.57  tff(c_156, plain, (![A_104, B_105]: (k2_xboole_0(k1_tarski(A_104), B_105)=B_105 | ~r2_hidden(A_104, B_105))), inference(resolution, [status(thm)], [c_138, c_2])).
% 3.47/1.57  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.57  tff(c_161, plain, (![B_105, A_104]: (k1_xboole_0!=B_105 | ~r2_hidden(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_156, c_10])).
% 3.47/1.57  tff(c_342, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_333, c_161])).
% 3.47/1.57  tff(c_72, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.47/1.57  tff(c_344, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.57  tff(c_358, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_344])).
% 3.47/1.57  tff(c_668, plain, (![B_230, A_231, C_232]: (k1_xboole_0=B_230 | k1_relset_1(A_231, B_230, C_232)=A_231 | ~v1_funct_2(C_232, A_231, B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.47/1.57  tff(c_679, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_668])).
% 3.47/1.57  tff(c_684, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_358, c_679])).
% 3.47/1.57  tff(c_685, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_342, c_684])).
% 3.47/1.57  tff(c_32, plain, (![A_26, C_62]: (r2_hidden('#skF_4'(A_26, k2_relat_1(A_26), C_62), k1_relat_1(A_26)) | ~r2_hidden(C_62, k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.47/1.57  tff(c_691, plain, (![C_62]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_62), '#skF_5') | ~r2_hidden(C_62, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_685, c_32])).
% 3.47/1.57  tff(c_729, plain, (![C_236]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_236), '#skF_5') | ~r2_hidden(C_236, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_74, c_691])).
% 3.47/1.57  tff(c_66, plain, (![E_79]: (k1_funct_1('#skF_8', E_79)!='#skF_7' | ~r2_hidden(E_79, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.47/1.57  tff(c_744, plain, (![C_237]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_237))!='#skF_7' | ~r2_hidden(C_237, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_729, c_66])).
% 3.47/1.57  tff(c_748, plain, (![C_62]: (C_62!='#skF_7' | ~r2_hidden(C_62, k2_relat_1('#skF_8')) | ~r2_hidden(C_62, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_744])).
% 3.47/1.57  tff(c_751, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_74, c_748])).
% 3.47/1.57  tff(c_306, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_68])).
% 3.47/1.57  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_751, c_306])).
% 3.47/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.57  
% 3.47/1.57  Inference rules
% 3.47/1.57  ----------------------
% 3.47/1.57  #Ref     : 0
% 3.47/1.57  #Sup     : 138
% 3.47/1.57  #Fact    : 0
% 3.47/1.57  #Define  : 0
% 3.47/1.57  #Split   : 5
% 3.47/1.57  #Chain   : 0
% 3.47/1.57  #Close   : 0
% 3.47/1.57  
% 3.47/1.57  Ordering : KBO
% 3.47/1.57  
% 3.47/1.57  Simplification rules
% 3.47/1.57  ----------------------
% 3.47/1.57  #Subsume      : 22
% 3.47/1.57  #Demod        : 30
% 3.47/1.57  #Tautology    : 33
% 3.47/1.57  #SimpNegUnit  : 3
% 3.47/1.57  #BackRed      : 8
% 3.47/1.57  
% 3.47/1.57  #Partial instantiations: 0
% 3.47/1.57  #Strategies tried      : 1
% 3.47/1.57  
% 3.47/1.57  Timing (in seconds)
% 3.47/1.57  ----------------------
% 3.47/1.58  Preprocessing        : 0.39
% 3.47/1.58  Parsing              : 0.20
% 3.47/1.58  CNF conversion       : 0.03
% 3.47/1.58  Main loop            : 0.40
% 3.47/1.58  Inferencing          : 0.15
% 3.47/1.58  Reduction            : 0.12
% 3.47/1.58  Demodulation         : 0.08
% 3.47/1.58  BG Simplification    : 0.02
% 3.47/1.58  Subsumption          : 0.08
% 3.47/1.58  Abstraction          : 0.02
% 3.47/1.58  MUC search           : 0.00
% 3.47/1.58  Cooper               : 0.00
% 3.47/1.58  Total                : 0.83
% 3.47/1.58  Index Insertion      : 0.00
% 3.47/1.58  Index Deletion       : 0.00
% 3.47/1.58  Index Matching       : 0.00
% 3.47/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
