%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:10 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   77 (  87 expanded)
%              Number of leaves         :   45 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 141 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_62,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_64,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(A_71,B_72)
      | k4_xboole_0(k1_tarski(A_71),B_72) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    ! [A_74] :
      ( r2_hidden(A_74,k1_xboole_0)
      | k1_tarski(A_74) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_133])).

tff(c_40,plain,(
    ! [B_45,A_44] :
      ( ~ r1_tarski(B_45,A_44)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_149,plain,(
    ! [A_74] :
      ( ~ r1_tarski(k1_xboole_0,A_74)
      | k1_tarski(A_74) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_143,c_40])).

tff(c_153,plain,(
    ! [A_74] : k1_tarski(A_74) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_228,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_232,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_228])).

tff(c_401,plain,(
    ! [B_157,A_158,C_159] :
      ( k1_xboole_0 = B_157
      | k1_relset_1(A_158,B_157,C_159) = A_158
      | ~ v1_funct_2(C_159,A_158,B_157)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_404,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_401])).

tff(c_407,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_232,c_404])).

tff(c_408,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_407])).

tff(c_154,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_158,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_154])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_171,plain,(
    ! [C_83,B_84,A_85] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_175,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_171])).

tff(c_283,plain,(
    ! [B_120,A_121] :
      ( r2_hidden(k1_funct_1(B_120,A_121),k2_relat_1(B_120))
      | ~ r2_hidden(A_121,k1_relat_1(B_120))
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    ! [C_41,A_38,B_39] :
      ( r2_hidden(C_41,A_38)
      | ~ r2_hidden(C_41,k2_relat_1(B_39))
      | ~ v5_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_339,plain,(
    ! [B_145,A_146,A_147] :
      ( r2_hidden(k1_funct_1(B_145,A_146),A_147)
      | ~ v5_relat_1(B_145,A_147)
      | ~ r2_hidden(A_146,k1_relat_1(B_145))
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(resolution,[status(thm)],[c_283,c_36])).

tff(c_6,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_379,plain,(
    ! [B_153,A_154,A_155] :
      ( k1_funct_1(B_153,A_154) = A_155
      | ~ v5_relat_1(B_153,k1_tarski(A_155))
      | ~ r2_hidden(A_154,k1_relat_1(B_153))
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153) ) ),
    inference(resolution,[status(thm)],[c_339,c_6])).

tff(c_381,plain,(
    ! [A_154] :
      ( k1_funct_1('#skF_6',A_154) = '#skF_4'
      | ~ r2_hidden(A_154,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_175,c_379])).

tff(c_384,plain,(
    ! [A_154] :
      ( k1_funct_1('#skF_6',A_154) = '#skF_4'
      | ~ r2_hidden(A_154,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_70,c_381])).

tff(c_425,plain,(
    ! [A_160] :
      ( k1_funct_1('#skF_6',A_160) = '#skF_4'
      | ~ r2_hidden(A_160,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_384])).

tff(c_440,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_64,c_425])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:15:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.43  
% 2.82/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.82/1.44  
% 2.82/1.44  %Foreground sorts:
% 2.82/1.44  
% 2.82/1.44  
% 2.82/1.44  %Background operators:
% 2.82/1.44  
% 2.82/1.44  
% 2.82/1.44  %Foreground operators:
% 2.82/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.82/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.82/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.44  
% 2.82/1.45  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.82/1.45  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.82/1.45  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.82/1.45  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.82/1.45  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.82/1.45  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.82/1.45  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.82/1.45  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.82/1.45  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.82/1.45  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.82/1.45  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 2.82/1.45  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.82/1.45  tff(c_62, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.82/1.45  tff(c_64, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.82/1.45  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.45  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.82/1.45  tff(c_133, plain, (![A_71, B_72]: (r2_hidden(A_71, B_72) | k4_xboole_0(k1_tarski(A_71), B_72)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.82/1.45  tff(c_143, plain, (![A_74]: (r2_hidden(A_74, k1_xboole_0) | k1_tarski(A_74)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_133])).
% 2.82/1.45  tff(c_40, plain, (![B_45, A_44]: (~r1_tarski(B_45, A_44) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.82/1.45  tff(c_149, plain, (![A_74]: (~r1_tarski(k1_xboole_0, A_74) | k1_tarski(A_74)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_40])).
% 2.82/1.45  tff(c_153, plain, (![A_74]: (k1_tarski(A_74)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_149])).
% 2.82/1.45  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.82/1.45  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.82/1.45  tff(c_228, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.45  tff(c_232, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_228])).
% 2.82/1.45  tff(c_401, plain, (![B_157, A_158, C_159]: (k1_xboole_0=B_157 | k1_relset_1(A_158, B_157, C_159)=A_158 | ~v1_funct_2(C_159, A_158, B_157) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.82/1.45  tff(c_404, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_401])).
% 2.82/1.45  tff(c_407, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_232, c_404])).
% 2.82/1.45  tff(c_408, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_153, c_407])).
% 2.82/1.45  tff(c_154, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.45  tff(c_158, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_154])).
% 2.82/1.45  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.82/1.45  tff(c_171, plain, (![C_83, B_84, A_85]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.82/1.45  tff(c_175, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_171])).
% 2.82/1.45  tff(c_283, plain, (![B_120, A_121]: (r2_hidden(k1_funct_1(B_120, A_121), k2_relat_1(B_120)) | ~r2_hidden(A_121, k1_relat_1(B_120)) | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.45  tff(c_36, plain, (![C_41, A_38, B_39]: (r2_hidden(C_41, A_38) | ~r2_hidden(C_41, k2_relat_1(B_39)) | ~v5_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.82/1.45  tff(c_339, plain, (![B_145, A_146, A_147]: (r2_hidden(k1_funct_1(B_145, A_146), A_147) | ~v5_relat_1(B_145, A_147) | ~r2_hidden(A_146, k1_relat_1(B_145)) | ~v1_funct_1(B_145) | ~v1_relat_1(B_145))), inference(resolution, [status(thm)], [c_283, c_36])).
% 2.82/1.45  tff(c_6, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.82/1.45  tff(c_379, plain, (![B_153, A_154, A_155]: (k1_funct_1(B_153, A_154)=A_155 | ~v5_relat_1(B_153, k1_tarski(A_155)) | ~r2_hidden(A_154, k1_relat_1(B_153)) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153))), inference(resolution, [status(thm)], [c_339, c_6])).
% 2.82/1.45  tff(c_381, plain, (![A_154]: (k1_funct_1('#skF_6', A_154)='#skF_4' | ~r2_hidden(A_154, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_175, c_379])).
% 2.82/1.45  tff(c_384, plain, (![A_154]: (k1_funct_1('#skF_6', A_154)='#skF_4' | ~r2_hidden(A_154, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_70, c_381])).
% 2.82/1.45  tff(c_425, plain, (![A_160]: (k1_funct_1('#skF_6', A_160)='#skF_4' | ~r2_hidden(A_160, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_384])).
% 2.82/1.45  tff(c_440, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_64, c_425])).
% 2.82/1.45  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_440])).
% 2.82/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.45  
% 2.82/1.45  Inference rules
% 2.82/1.45  ----------------------
% 2.82/1.45  #Ref     : 0
% 2.82/1.45  #Sup     : 76
% 2.82/1.45  #Fact    : 0
% 2.82/1.45  #Define  : 0
% 2.82/1.45  #Split   : 1
% 2.82/1.45  #Chain   : 0
% 2.82/1.45  #Close   : 0
% 2.82/1.45  
% 2.82/1.45  Ordering : KBO
% 2.82/1.45  
% 2.82/1.45  Simplification rules
% 2.82/1.45  ----------------------
% 2.82/1.45  #Subsume      : 8
% 2.82/1.45  #Demod        : 14
% 2.82/1.45  #Tautology    : 35
% 2.82/1.45  #SimpNegUnit  : 8
% 2.82/1.45  #BackRed      : 3
% 2.82/1.45  
% 2.82/1.45  #Partial instantiations: 0
% 2.82/1.45  #Strategies tried      : 1
% 2.82/1.45  
% 2.82/1.45  Timing (in seconds)
% 2.82/1.45  ----------------------
% 2.82/1.46  Preprocessing        : 0.37
% 2.82/1.46  Parsing              : 0.20
% 2.82/1.46  CNF conversion       : 0.03
% 2.82/1.46  Main loop            : 0.31
% 2.82/1.46  Inferencing          : 0.12
% 2.82/1.46  Reduction            : 0.09
% 2.82/1.46  Demodulation         : 0.06
% 2.82/1.46  BG Simplification    : 0.02
% 2.82/1.46  Subsumption          : 0.07
% 2.82/1.46  Abstraction          : 0.02
% 2.82/1.46  MUC search           : 0.00
% 2.82/1.46  Cooper               : 0.00
% 2.82/1.46  Total                : 0.72
% 2.82/1.46  Index Insertion      : 0.00
% 2.82/1.46  Index Deletion       : 0.00
% 2.82/1.46  Index Matching       : 0.00
% 2.82/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
