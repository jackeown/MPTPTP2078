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
% DateTime   : Thu Dec  3 10:14:59 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 220 expanded)
%              Number of leaves         :   40 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 435 expanded)
%              Number of equality atoms :   43 (  99 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_110,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_40,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_565,plain,(
    ! [B_123,A_124] :
      ( v1_relat_1(B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_124))
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_568,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_565])).

tff(c_577,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_568])).

tff(c_42,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k9_relat_1(B_27,A_26),k2_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) = k1_xboole_0
      | k2_relat_1(A_28) != k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_587,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_577,c_44])).

tff(c_589,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_587])).

tff(c_46,plain,(
    ! [A_28] :
      ( k2_relat_1(A_28) = k1_xboole_0
      | k1_relat_1(A_28) != k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_588,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_577,c_46])).

tff(c_612,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_588])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_908,plain,(
    ! [B_174,A_175] :
      ( k1_tarski(k1_funct_1(B_174,A_175)) = k2_relat_1(B_174)
      | k1_tarski(A_175) != k1_relat_1(B_174)
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_917,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_908,c_58])).

tff(c_923,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_66,c_917])).

tff(c_928,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_923])).

tff(c_698,plain,(
    ! [C_144,A_145,B_146] :
      ( v4_relat_1(C_144,A_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_716,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_698])).

tff(c_807,plain,(
    ! [B_165,A_166] :
      ( r1_tarski(k1_relat_1(B_165),A_166)
      | ~ v4_relat_1(B_165,A_166)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k1_tarski(B_10) = A_9
      | k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_tarski(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1623,plain,(
    ! [B_265,B_266] :
      ( k1_tarski(B_265) = k1_relat_1(B_266)
      | k1_relat_1(B_266) = k1_xboole_0
      | ~ v4_relat_1(B_266,k1_tarski(B_265))
      | ~ v1_relat_1(B_266) ) ),
    inference(resolution,[status(thm)],[c_807,c_14])).

tff(c_1649,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_716,c_1623])).

tff(c_1663,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_1649])).

tff(c_1665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_612,c_928,c_1663])).

tff(c_1667,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_1673,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_62])).

tff(c_54,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k7_relset_1(A_34,B_35,C_36,D_37) = k9_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1739,plain,(
    ! [D_37] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_37) = k9_relat_1('#skF_4',D_37) ),
    inference(resolution,[status(thm)],[c_1673,c_54])).

tff(c_1666,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_1756,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_1666])).

tff(c_1798,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_1756])).

tff(c_1811,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1798])).

tff(c_1815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_1811])).

tff(c_1816,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_587])).

tff(c_1823,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1816,c_588])).

tff(c_1827,plain,(
    ! [A_26] :
      ( r1_tarski(k9_relat_1('#skF_4',A_26),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1823,c_42])).

tff(c_1834,plain,(
    ! [A_281] : r1_tarski(k9_relat_1('#skF_4',A_281),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_1827])).

tff(c_494,plain,(
    ! [B_116,A_117] :
      ( B_116 = A_117
      | ~ r1_tarski(B_116,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_510,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_118,c_494])).

tff(c_1840,plain,(
    ! [A_281] : k9_relat_1('#skF_4',A_281) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1834,c_510])).

tff(c_2349,plain,(
    ! [A_351,B_352,C_353,D_354] :
      ( k7_relset_1(A_351,B_352,C_353,D_354) = k9_relat_1(C_353,D_354)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2351,plain,(
    ! [D_354] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_354) = k9_relat_1('#skF_4',D_354) ),
    inference(resolution,[status(thm)],[c_62,c_2349])).

tff(c_2363,plain,(
    ! [D_354] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_354) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_2351])).

tff(c_2374,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_58])).

tff(c_2377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:37:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.69  
% 3.89/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.13/1.69  
% 4.13/1.69  %Foreground sorts:
% 4.13/1.69  
% 4.13/1.69  
% 4.13/1.69  %Background operators:
% 4.13/1.69  
% 4.13/1.69  
% 4.13/1.69  %Foreground operators:
% 4.13/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.13/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.13/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.13/1.69  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.13/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.13/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.13/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.13/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.13/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.69  tff('#skF_1', type, '#skF_1': $i).
% 4.13/1.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.13/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.13/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.13/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.69  
% 4.13/1.72  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.13/1.72  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.13/1.72  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.13/1.72  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 4.13/1.72  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.13/1.72  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 4.13/1.72  tff(f_86, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 4.13/1.72  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.13/1.72  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.13/1.72  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.13/1.72  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.13/1.72  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.13/1.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.13/1.72  tff(c_26, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.13/1.72  tff(c_110, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.13/1.72  tff(c_118, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_26, c_110])).
% 4.13/1.72  tff(c_40, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.13/1.72  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.13/1.72  tff(c_565, plain, (![B_123, A_124]: (v1_relat_1(B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(A_124)) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.13/1.72  tff(c_568, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_565])).
% 4.13/1.72  tff(c_577, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_568])).
% 4.13/1.72  tff(c_42, plain, (![B_27, A_26]: (r1_tarski(k9_relat_1(B_27, A_26), k2_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.13/1.72  tff(c_44, plain, (![A_28]: (k1_relat_1(A_28)=k1_xboole_0 | k2_relat_1(A_28)!=k1_xboole_0 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.13/1.72  tff(c_587, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_577, c_44])).
% 4.13/1.72  tff(c_589, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_587])).
% 4.13/1.72  tff(c_46, plain, (![A_28]: (k2_relat_1(A_28)=k1_xboole_0 | k1_relat_1(A_28)!=k1_xboole_0 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.13/1.72  tff(c_588, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_577, c_46])).
% 4.13/1.72  tff(c_612, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_589, c_588])).
% 4.13/1.72  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.13/1.72  tff(c_908, plain, (![B_174, A_175]: (k1_tarski(k1_funct_1(B_174, A_175))=k2_relat_1(B_174) | k1_tarski(A_175)!=k1_relat_1(B_174) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.13/1.72  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.13/1.72  tff(c_917, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_908, c_58])).
% 4.13/1.72  tff(c_923, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_66, c_917])).
% 4.13/1.72  tff(c_928, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_923])).
% 4.13/1.72  tff(c_698, plain, (![C_144, A_145, B_146]: (v4_relat_1(C_144, A_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.13/1.72  tff(c_716, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_698])).
% 4.13/1.72  tff(c_807, plain, (![B_165, A_166]: (r1_tarski(k1_relat_1(B_165), A_166) | ~v4_relat_1(B_165, A_166) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.72  tff(c_14, plain, (![B_10, A_9]: (k1_tarski(B_10)=A_9 | k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.72  tff(c_1623, plain, (![B_265, B_266]: (k1_tarski(B_265)=k1_relat_1(B_266) | k1_relat_1(B_266)=k1_xboole_0 | ~v4_relat_1(B_266, k1_tarski(B_265)) | ~v1_relat_1(B_266))), inference(resolution, [status(thm)], [c_807, c_14])).
% 4.13/1.72  tff(c_1649, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_716, c_1623])).
% 4.13/1.72  tff(c_1663, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_577, c_1649])).
% 4.13/1.72  tff(c_1665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_612, c_928, c_1663])).
% 4.13/1.72  tff(c_1667, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_923])).
% 4.13/1.72  tff(c_1673, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_62])).
% 4.13/1.72  tff(c_54, plain, (![A_34, B_35, C_36, D_37]: (k7_relset_1(A_34, B_35, C_36, D_37)=k9_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.13/1.72  tff(c_1739, plain, (![D_37]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_37)=k9_relat_1('#skF_4', D_37))), inference(resolution, [status(thm)], [c_1673, c_54])).
% 4.13/1.72  tff(c_1666, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_923])).
% 4.13/1.72  tff(c_1756, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_1666])).
% 4.13/1.72  tff(c_1798, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_1756])).
% 4.13/1.72  tff(c_1811, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1798])).
% 4.13/1.72  tff(c_1815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_1811])).
% 4.13/1.72  tff(c_1816, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_587])).
% 4.13/1.72  tff(c_1823, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1816, c_588])).
% 4.13/1.72  tff(c_1827, plain, (![A_26]: (r1_tarski(k9_relat_1('#skF_4', A_26), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1823, c_42])).
% 4.13/1.72  tff(c_1834, plain, (![A_281]: (r1_tarski(k9_relat_1('#skF_4', A_281), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_577, c_1827])).
% 4.13/1.72  tff(c_494, plain, (![B_116, A_117]: (B_116=A_117 | ~r1_tarski(B_116, A_117) | ~r1_tarski(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.13/1.72  tff(c_510, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_118, c_494])).
% 4.13/1.72  tff(c_1840, plain, (![A_281]: (k9_relat_1('#skF_4', A_281)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1834, c_510])).
% 4.13/1.72  tff(c_2349, plain, (![A_351, B_352, C_353, D_354]: (k7_relset_1(A_351, B_352, C_353, D_354)=k9_relat_1(C_353, D_354) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.13/1.72  tff(c_2351, plain, (![D_354]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_354)=k9_relat_1('#skF_4', D_354))), inference(resolution, [status(thm)], [c_62, c_2349])).
% 4.13/1.72  tff(c_2363, plain, (![D_354]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_354)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1840, c_2351])).
% 4.13/1.72  tff(c_2374, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_58])).
% 4.13/1.72  tff(c_2377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_2374])).
% 4.13/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.72  
% 4.13/1.72  Inference rules
% 4.13/1.72  ----------------------
% 4.13/1.72  #Ref     : 0
% 4.13/1.72  #Sup     : 480
% 4.13/1.72  #Fact    : 0
% 4.13/1.72  #Define  : 0
% 4.13/1.72  #Split   : 11
% 4.13/1.72  #Chain   : 0
% 4.13/1.72  #Close   : 0
% 4.13/1.72  
% 4.13/1.72  Ordering : KBO
% 4.13/1.72  
% 4.13/1.72  Simplification rules
% 4.13/1.72  ----------------------
% 4.13/1.72  #Subsume      : 75
% 4.13/1.72  #Demod        : 372
% 4.13/1.72  #Tautology    : 239
% 4.13/1.72  #SimpNegUnit  : 23
% 4.13/1.72  #BackRed      : 19
% 4.13/1.72  
% 4.13/1.72  #Partial instantiations: 0
% 4.13/1.72  #Strategies tried      : 1
% 4.13/1.72  
% 4.13/1.72  Timing (in seconds)
% 4.13/1.72  ----------------------
% 4.13/1.72  Preprocessing        : 0.34
% 4.13/1.72  Parsing              : 0.18
% 4.13/1.72  CNF conversion       : 0.02
% 4.13/1.72  Main loop            : 0.60
% 4.13/1.72  Inferencing          : 0.22
% 4.13/1.72  Reduction            : 0.20
% 4.13/1.72  Demodulation         : 0.14
% 4.13/1.72  BG Simplification    : 0.03
% 4.13/1.72  Subsumption          : 0.10
% 4.13/1.72  Abstraction          : 0.02
% 4.13/1.72  MUC search           : 0.00
% 4.13/1.72  Cooper               : 0.00
% 4.13/1.72  Total                : 0.99
% 4.13/1.72  Index Insertion      : 0.00
% 4.13/1.72  Index Deletion       : 0.00
% 4.13/1.72  Index Matching       : 0.00
% 4.13/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
