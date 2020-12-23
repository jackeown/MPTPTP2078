%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:07 EST 2020

% Result     : Theorem 18.66s
% Output     : CNFRefutation 18.66s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 113 expanded)
%              Number of leaves         :   47 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 210 expanded)
%              Number of equality atoms :   29 (  57 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_140,axiom,(
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

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    ! [A_78,B_79] :
      ( ~ r2_hidden(A_78,B_79)
      | ~ r1_xboole_0(k1_tarski(A_78),B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_154,plain,(
    ! [A_78] : ~ r2_hidden(A_78,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_149])).

tff(c_118,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_122,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_212,plain,(
    ! [C_102,B_103,A_104] :
      ( v5_relat_1(C_102,B_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_221,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_122,c_212])).

tff(c_170,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_179,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_122,c_170])).

tff(c_94,plain,(
    ! [B_56,A_55] :
      ( r1_tarski(k2_relat_1(B_56),A_55)
      | ~ v5_relat_1(B_56,A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_120,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_126,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_124,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_337,plain,(
    ! [A_197,B_198,C_199] :
      ( k1_relset_1(A_197,B_198,C_199) = k1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_346,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_122,c_337])).

tff(c_646,plain,(
    ! [B_289,A_290,C_291] :
      ( k1_xboole_0 = B_289
      | k1_relset_1(A_290,B_289,C_291) = A_290
      | ~ v1_funct_2(C_291,A_290,B_289)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_290,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_653,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_122,c_646])).

tff(c_657,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_346,c_653])).

tff(c_658,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_90,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(A_53,k1_zfmisc_1(B_54))
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_474,plain,(
    ! [B_224,A_225] :
      ( r2_hidden(k1_funct_1(B_224,A_225),k2_relat_1(B_224))
      | ~ r2_hidden(A_225,k1_relat_1(B_224))
      | ~ v1_funct_1(B_224)
      | ~ v1_relat_1(B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_86,plain,(
    ! [C_52,A_49,B_50] :
      ( r2_hidden(C_52,A_49)
      | ~ r2_hidden(C_52,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_17801,plain,(
    ! [B_72265,A_72266,A_72267] :
      ( r2_hidden(k1_funct_1(B_72265,A_72266),A_72267)
      | ~ m1_subset_1(k2_relat_1(B_72265),k1_zfmisc_1(A_72267))
      | ~ r2_hidden(A_72266,k1_relat_1(B_72265))
      | ~ v1_funct_1(B_72265)
      | ~ v1_relat_1(B_72265) ) ),
    inference(resolution,[status(thm)],[c_474,c_86])).

tff(c_17816,plain,(
    ! [B_72608,A_72609,B_72610] :
      ( r2_hidden(k1_funct_1(B_72608,A_72609),B_72610)
      | ~ r2_hidden(A_72609,k1_relat_1(B_72608))
      | ~ v1_funct_1(B_72608)
      | ~ v1_relat_1(B_72608)
      | ~ r1_tarski(k2_relat_1(B_72608),B_72610) ) ),
    inference(resolution,[status(thm)],[c_90,c_17801])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22801,plain,(
    ! [B_89760,A_89761,A_89762] :
      ( k1_funct_1(B_89760,A_89761) = A_89762
      | ~ r2_hidden(A_89761,k1_relat_1(B_89760))
      | ~ v1_funct_1(B_89760)
      | ~ v1_relat_1(B_89760)
      | ~ r1_tarski(k2_relat_1(B_89760),k1_tarski(A_89762)) ) ),
    inference(resolution,[status(thm)],[c_17816,c_4])).

tff(c_22815,plain,(
    ! [A_89761,A_89762] :
      ( k1_funct_1('#skF_8',A_89761) = A_89762
      | ~ r2_hidden(A_89761,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_tarski(A_89762)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_22801])).

tff(c_22832,plain,(
    ! [A_90171,A_90172] :
      ( k1_funct_1('#skF_8',A_90171) = A_90172
      | ~ r2_hidden(A_90171,'#skF_5')
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_tarski(A_90172)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_126,c_22815])).

tff(c_22856,plain,(
    ! [A_90581] :
      ( k1_funct_1('#skF_8','#skF_7') = A_90581
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_tarski(A_90581)) ) ),
    inference(resolution,[status(thm)],[c_120,c_22832])).

tff(c_22865,plain,(
    ! [A_90581] :
      ( k1_funct_1('#skF_8','#skF_7') = A_90581
      | ~ v5_relat_1('#skF_8',k1_tarski(A_90581))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_94,c_22856])).

tff(c_22869,plain,(
    ! [A_90990] :
      ( k1_funct_1('#skF_8','#skF_7') = A_90990
      | ~ v5_relat_1('#skF_8',k1_tarski(A_90990)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_22865])).

tff(c_22878,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_221,c_22869])).

tff(c_22882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_22878])).

tff(c_22883,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22911,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22883,c_6])).

tff(c_22916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_22911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.66/10.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.66/10.30  
% 18.66/10.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.66/10.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1
% 18.66/10.30  
% 18.66/10.30  %Foreground sorts:
% 18.66/10.30  
% 18.66/10.30  
% 18.66/10.30  %Background operators:
% 18.66/10.30  
% 18.66/10.30  
% 18.66/10.30  %Foreground operators:
% 18.66/10.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.66/10.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.66/10.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.66/10.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.66/10.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.66/10.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.66/10.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.66/10.30  tff('#skF_7', type, '#skF_7': $i).
% 18.66/10.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.66/10.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.66/10.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.66/10.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.66/10.30  tff('#skF_5', type, '#skF_5': $i).
% 18.66/10.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.66/10.30  tff('#skF_6', type, '#skF_6': $i).
% 18.66/10.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.66/10.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 18.66/10.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.66/10.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 18.66/10.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 18.66/10.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.66/10.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.66/10.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 18.66/10.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.66/10.30  tff('#skF_8', type, '#skF_8': $i).
% 18.66/10.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.66/10.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.66/10.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.66/10.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.66/10.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 18.66/10.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 18.66/10.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.66/10.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.66/10.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.66/10.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.66/10.30  
% 18.66/10.31  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 18.66/10.31  tff(f_53, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 18.66/10.31  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 18.66/10.31  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.66/10.31  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.66/10.31  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 18.66/10.31  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 18.66/10.31  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 18.66/10.31  tff(f_94, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 18.66/10.31  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 18.66/10.31  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 18.66/10.31  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 18.66/10.31  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.66/10.31  tff(c_149, plain, (![A_78, B_79]: (~r2_hidden(A_78, B_79) | ~r1_xboole_0(k1_tarski(A_78), B_79))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.66/10.31  tff(c_154, plain, (![A_78]: (~r2_hidden(A_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_149])).
% 18.66/10.31  tff(c_118, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.66/10.31  tff(c_122, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.66/10.31  tff(c_212, plain, (![C_102, B_103, A_104]: (v5_relat_1(C_102, B_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 18.66/10.31  tff(c_221, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_122, c_212])).
% 18.66/10.31  tff(c_170, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 18.66/10.31  tff(c_179, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_122, c_170])).
% 18.66/10.31  tff(c_94, plain, (![B_56, A_55]: (r1_tarski(k2_relat_1(B_56), A_55) | ~v5_relat_1(B_56, A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.66/10.31  tff(c_120, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.66/10.31  tff(c_126, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.66/10.31  tff(c_124, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 18.66/10.31  tff(c_337, plain, (![A_197, B_198, C_199]: (k1_relset_1(A_197, B_198, C_199)=k1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 18.66/10.31  tff(c_346, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_122, c_337])).
% 18.66/10.31  tff(c_646, plain, (![B_289, A_290, C_291]: (k1_xboole_0=B_289 | k1_relset_1(A_290, B_289, C_291)=A_290 | ~v1_funct_2(C_291, A_290, B_289) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_290, B_289))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.66/10.31  tff(c_653, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_122, c_646])).
% 18.66/10.31  tff(c_657, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_346, c_653])).
% 18.66/10.31  tff(c_658, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_657])).
% 18.66/10.31  tff(c_90, plain, (![A_53, B_54]: (m1_subset_1(A_53, k1_zfmisc_1(B_54)) | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_94])).
% 18.66/10.31  tff(c_474, plain, (![B_224, A_225]: (r2_hidden(k1_funct_1(B_224, A_225), k2_relat_1(B_224)) | ~r2_hidden(A_225, k1_relat_1(B_224)) | ~v1_funct_1(B_224) | ~v1_relat_1(B_224))), inference(cnfTransformation, [status(thm)], [f_108])).
% 18.66/10.31  tff(c_86, plain, (![C_52, A_49, B_50]: (r2_hidden(C_52, A_49) | ~r2_hidden(C_52, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 18.66/10.31  tff(c_17801, plain, (![B_72265, A_72266, A_72267]: (r2_hidden(k1_funct_1(B_72265, A_72266), A_72267) | ~m1_subset_1(k2_relat_1(B_72265), k1_zfmisc_1(A_72267)) | ~r2_hidden(A_72266, k1_relat_1(B_72265)) | ~v1_funct_1(B_72265) | ~v1_relat_1(B_72265))), inference(resolution, [status(thm)], [c_474, c_86])).
% 18.66/10.31  tff(c_17816, plain, (![B_72608, A_72609, B_72610]: (r2_hidden(k1_funct_1(B_72608, A_72609), B_72610) | ~r2_hidden(A_72609, k1_relat_1(B_72608)) | ~v1_funct_1(B_72608) | ~v1_relat_1(B_72608) | ~r1_tarski(k2_relat_1(B_72608), B_72610))), inference(resolution, [status(thm)], [c_90, c_17801])).
% 18.66/10.31  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.66/10.31  tff(c_22801, plain, (![B_89760, A_89761, A_89762]: (k1_funct_1(B_89760, A_89761)=A_89762 | ~r2_hidden(A_89761, k1_relat_1(B_89760)) | ~v1_funct_1(B_89760) | ~v1_relat_1(B_89760) | ~r1_tarski(k2_relat_1(B_89760), k1_tarski(A_89762)))), inference(resolution, [status(thm)], [c_17816, c_4])).
% 18.66/10.31  tff(c_22815, plain, (![A_89761, A_89762]: (k1_funct_1('#skF_8', A_89761)=A_89762 | ~r2_hidden(A_89761, '#skF_5') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), k1_tarski(A_89762)))), inference(superposition, [status(thm), theory('equality')], [c_658, c_22801])).
% 18.66/10.31  tff(c_22832, plain, (![A_90171, A_90172]: (k1_funct_1('#skF_8', A_90171)=A_90172 | ~r2_hidden(A_90171, '#skF_5') | ~r1_tarski(k2_relat_1('#skF_8'), k1_tarski(A_90172)))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_126, c_22815])).
% 18.66/10.31  tff(c_22856, plain, (![A_90581]: (k1_funct_1('#skF_8', '#skF_7')=A_90581 | ~r1_tarski(k2_relat_1('#skF_8'), k1_tarski(A_90581)))), inference(resolution, [status(thm)], [c_120, c_22832])).
% 18.66/10.31  tff(c_22865, plain, (![A_90581]: (k1_funct_1('#skF_8', '#skF_7')=A_90581 | ~v5_relat_1('#skF_8', k1_tarski(A_90581)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_94, c_22856])).
% 18.66/10.31  tff(c_22869, plain, (![A_90990]: (k1_funct_1('#skF_8', '#skF_7')=A_90990 | ~v5_relat_1('#skF_8', k1_tarski(A_90990)))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_22865])).
% 18.66/10.31  tff(c_22878, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_221, c_22869])).
% 18.66/10.31  tff(c_22882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_22878])).
% 18.66/10.31  tff(c_22883, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_657])).
% 18.66/10.31  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.66/10.31  tff(c_22911, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22883, c_6])).
% 18.66/10.31  tff(c_22916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_22911])).
% 18.66/10.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.66/10.31  
% 18.66/10.31  Inference rules
% 18.66/10.31  ----------------------
% 18.66/10.31  #Ref     : 0
% 18.66/10.31  #Sup     : 4052
% 18.66/10.31  #Fact    : 336
% 18.66/10.31  #Define  : 0
% 18.66/10.31  #Split   : 3
% 18.66/10.31  #Chain   : 0
% 18.66/10.31  #Close   : 0
% 18.66/10.31  
% 18.66/10.31  Ordering : KBO
% 18.66/10.31  
% 18.66/10.31  Simplification rules
% 18.66/10.31  ----------------------
% 18.66/10.31  #Subsume      : 2433
% 18.66/10.31  #Demod        : 61
% 18.66/10.31  #Tautology    : 404
% 18.66/10.31  #SimpNegUnit  : 51
% 18.66/10.31  #BackRed      : 6
% 18.66/10.31  
% 18.66/10.31  #Partial instantiations: 30498
% 18.66/10.31  #Strategies tried      : 1
% 18.66/10.31  
% 18.66/10.31  Timing (in seconds)
% 18.66/10.31  ----------------------
% 18.66/10.32  Preprocessing        : 0.40
% 18.66/10.32  Parsing              : 0.19
% 18.66/10.32  CNF conversion       : 0.03
% 18.66/10.32  Main loop            : 9.15
% 18.66/10.32  Inferencing          : 3.59
% 18.66/10.32  Reduction            : 1.46
% 18.66/10.32  Demodulation         : 1.21
% 18.66/10.32  BG Simplification    : 0.27
% 18.66/10.32  Subsumption          : 3.67
% 18.66/10.32  Abstraction          : 0.73
% 18.66/10.32  MUC search           : 0.00
% 18.66/10.32  Cooper               : 0.00
% 18.66/10.32  Total                : 9.58
% 18.66/10.32  Index Insertion      : 0.00
% 18.66/10.32  Index Deletion       : 0.00
% 18.66/10.32  Index Matching       : 0.00
% 18.66/10.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
