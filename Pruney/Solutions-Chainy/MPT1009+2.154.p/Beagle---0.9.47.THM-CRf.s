%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:03 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 140 expanded)
%              Number of leaves         :   43 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 275 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_34,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_121,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_127,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_121])).

tff(c_131,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_127])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    ! [A_40] :
      ( m1_subset_1(A_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40))))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_239,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k7_relset_1(A_82,B_83,C_84,D_85) = k9_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_247,plain,(
    ! [A_40,D_85] :
      ( k7_relset_1(k1_relat_1(A_40),k2_relat_1(A_40),A_40,D_85) = k9_relat_1(A_40,D_85)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_58,c_239])).

tff(c_260,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( m1_subset_1(k7_relset_1(A_87,B_88,C_89,D_90),k1_zfmisc_1(B_88))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_370,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( r1_tarski(k7_relset_1(A_103,B_104,C_105,D_106),B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(resolution,[status(thm)],[c_260,c_26])).

tff(c_454,plain,(
    ! [A_124,D_125] :
      ( r1_tarski(k7_relset_1(k1_relat_1(A_124),k2_relat_1(A_124),A_124,D_125),k2_relat_1(A_124))
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_58,c_370])).

tff(c_460,plain,(
    ! [A_40,D_85] :
      ( r1_tarski(k9_relat_1(A_40,D_85),k2_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_454])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_70,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_178,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_187,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_178])).

tff(c_569,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_583,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_569])).

tff(c_589,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_187,c_583])).

tff(c_590,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_589])).

tff(c_32,plain,(
    ! [A_18,B_20] :
      ( k9_relat_1(A_18,k1_tarski(B_20)) = k11_relat_1(A_18,B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1963,plain,(
    ! [A_5393] :
      ( k9_relat_1(A_5393,k1_relat_1('#skF_6')) = k11_relat_1(A_5393,'#skF_3')
      | ~ v1_relat_1(A_5393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_32])).

tff(c_36,plain,(
    ! [A_23] :
      ( k9_relat_1(A_23,k1_relat_1(A_23)) = k2_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1984,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_36])).

tff(c_2000,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_1984])).

tff(c_76,plain,(
    ! [A_47] : k2_tarski(A_47,A_47) = k1_tarski(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [A_47] : r2_hidden(A_47,k1_tarski(A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_4])).

tff(c_605,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_82])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(k1_funct_1(B_25,A_24)) = k11_relat_1(B_25,A_24)
      | ~ r2_hidden(A_24,k1_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_611,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_605,c_38])).

tff(c_614,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_72,c_611])).

tff(c_249,plain,(
    ! [D_85] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_85) = k9_relat_1('#skF_6',D_85) ),
    inference(resolution,[status(thm)],[c_68,c_239])).

tff(c_64,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_250,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_64])).

tff(c_1224,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k11_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_250])).

tff(c_2005,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_1224])).

tff(c_2032,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_460,c_2005])).

tff(c_2036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_72,c_2032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:57:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.61  
% 3.64/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.61  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.64/1.61  
% 3.64/1.61  %Foreground sorts:
% 3.64/1.61  
% 3.64/1.61  
% 3.64/1.61  %Background operators:
% 3.64/1.61  
% 3.64/1.61  
% 3.64/1.61  %Foreground operators:
% 3.64/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.64/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.64/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.64/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.61  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.64/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.64/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.64/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.64/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.64/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.61  
% 3.97/1.63  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.97/1.63  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.97/1.63  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.97/1.63  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.97/1.63  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.97/1.63  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.97/1.63  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.97/1.63  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.97/1.63  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.97/1.63  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.97/1.63  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.97/1.63  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.97/1.63  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.97/1.63  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.97/1.63  tff(c_34, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.97/1.63  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.97/1.63  tff(c_121, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.97/1.63  tff(c_127, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_121])).
% 3.97/1.63  tff(c_131, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_127])).
% 3.97/1.63  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.97/1.63  tff(c_58, plain, (![A_40]: (m1_subset_1(A_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40)))) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.97/1.63  tff(c_239, plain, (![A_82, B_83, C_84, D_85]: (k7_relset_1(A_82, B_83, C_84, D_85)=k9_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.97/1.63  tff(c_247, plain, (![A_40, D_85]: (k7_relset_1(k1_relat_1(A_40), k2_relat_1(A_40), A_40, D_85)=k9_relat_1(A_40, D_85) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_58, c_239])).
% 3.97/1.63  tff(c_260, plain, (![A_87, B_88, C_89, D_90]: (m1_subset_1(k7_relset_1(A_87, B_88, C_89, D_90), k1_zfmisc_1(B_88)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.97/1.63  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.97/1.63  tff(c_370, plain, (![A_103, B_104, C_105, D_106]: (r1_tarski(k7_relset_1(A_103, B_104, C_105, D_106), B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(resolution, [status(thm)], [c_260, c_26])).
% 3.97/1.63  tff(c_454, plain, (![A_124, D_125]: (r1_tarski(k7_relset_1(k1_relat_1(A_124), k2_relat_1(A_124), A_124, D_125), k2_relat_1(A_124)) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_58, c_370])).
% 3.97/1.63  tff(c_460, plain, (![A_40, D_85]: (r1_tarski(k9_relat_1(A_40, D_85), k2_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_247, c_454])).
% 3.97/1.63  tff(c_66, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.97/1.63  tff(c_70, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.97/1.63  tff(c_178, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.97/1.63  tff(c_187, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_178])).
% 3.97/1.63  tff(c_569, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.97/1.63  tff(c_583, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_68, c_569])).
% 3.97/1.63  tff(c_589, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_187, c_583])).
% 3.97/1.63  tff(c_590, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_589])).
% 3.97/1.63  tff(c_32, plain, (![A_18, B_20]: (k9_relat_1(A_18, k1_tarski(B_20))=k11_relat_1(A_18, B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.97/1.63  tff(c_1963, plain, (![A_5393]: (k9_relat_1(A_5393, k1_relat_1('#skF_6'))=k11_relat_1(A_5393, '#skF_3') | ~v1_relat_1(A_5393))), inference(superposition, [status(thm), theory('equality')], [c_590, c_32])).
% 3.97/1.63  tff(c_36, plain, (![A_23]: (k9_relat_1(A_23, k1_relat_1(A_23))=k2_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.97/1.63  tff(c_1984, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1963, c_36])).
% 3.97/1.63  tff(c_2000, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_1984])).
% 3.97/1.63  tff(c_76, plain, (![A_47]: (k2_tarski(A_47, A_47)=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.63  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.97/1.63  tff(c_82, plain, (![A_47]: (r2_hidden(A_47, k1_tarski(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_4])).
% 3.97/1.63  tff(c_605, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_590, c_82])).
% 3.97/1.63  tff(c_38, plain, (![B_25, A_24]: (k1_tarski(k1_funct_1(B_25, A_24))=k11_relat_1(B_25, A_24) | ~r2_hidden(A_24, k1_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.97/1.63  tff(c_611, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_605, c_38])).
% 3.97/1.63  tff(c_614, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_72, c_611])).
% 3.97/1.63  tff(c_249, plain, (![D_85]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_85)=k9_relat_1('#skF_6', D_85))), inference(resolution, [status(thm)], [c_68, c_239])).
% 3.97/1.63  tff(c_64, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.97/1.63  tff(c_250, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_64])).
% 3.97/1.63  tff(c_1224, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k11_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_250])).
% 3.97/1.63  tff(c_2005, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_1224])).
% 3.97/1.63  tff(c_2032, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_460, c_2005])).
% 3.97/1.63  tff(c_2036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_72, c_2032])).
% 3.97/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.63  
% 3.97/1.63  Inference rules
% 3.97/1.63  ----------------------
% 3.97/1.63  #Ref     : 0
% 3.97/1.63  #Sup     : 255
% 3.97/1.63  #Fact    : 4
% 3.97/1.63  #Define  : 0
% 3.97/1.63  #Split   : 1
% 3.97/1.63  #Chain   : 0
% 3.97/1.63  #Close   : 0
% 3.97/1.63  
% 3.97/1.63  Ordering : KBO
% 3.97/1.63  
% 3.97/1.63  Simplification rules
% 3.97/1.63  ----------------------
% 3.97/1.63  #Subsume      : 34
% 3.97/1.63  #Demod        : 82
% 3.97/1.63  #Tautology    : 80
% 3.97/1.63  #SimpNegUnit  : 6
% 3.97/1.63  #BackRed      : 11
% 3.97/1.63  
% 3.97/1.63  #Partial instantiations: 3160
% 3.97/1.63  #Strategies tried      : 1
% 3.97/1.63  
% 3.97/1.63  Timing (in seconds)
% 3.97/1.63  ----------------------
% 3.97/1.63  Preprocessing        : 0.35
% 3.97/1.63  Parsing              : 0.18
% 3.97/1.63  CNF conversion       : 0.02
% 3.97/1.63  Main loop            : 0.52
% 3.97/1.63  Inferencing          : 0.27
% 3.97/1.63  Reduction            : 0.13
% 3.97/1.63  Demodulation         : 0.09
% 3.97/1.63  BG Simplification    : 0.03
% 3.97/1.63  Subsumption          : 0.07
% 3.97/1.63  Abstraction          : 0.02
% 3.97/1.63  MUC search           : 0.00
% 3.97/1.63  Cooper               : 0.00
% 3.97/1.63  Total                : 0.90
% 3.97/1.63  Index Insertion      : 0.00
% 3.97/1.63  Index Deletion       : 0.00
% 3.97/1.63  Index Matching       : 0.00
% 3.97/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
