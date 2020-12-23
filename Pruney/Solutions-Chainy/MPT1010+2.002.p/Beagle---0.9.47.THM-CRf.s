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
% DateTime   : Thu Dec  3 10:15:05 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   82 (  92 expanded)
%              Number of leaves         :   48 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 143 expanded)
%              Number of equality atoms :   40 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_68,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_70,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_131,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_131])).

tff(c_143,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_140])).

tff(c_40,plain,(
    ! [B_42] : k4_xboole_0(k1_tarski(B_42),k1_tarski(B_42)) != k1_tarski(B_42) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_144,plain,(
    ! [B_42] : k1_tarski(B_42) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_40])).

tff(c_74,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_212,plain,(
    ! [A_102,B_103,C_104] :
      ( k1_relset_1(A_102,B_103,C_104) = k1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_216,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_212])).

tff(c_361,plain,(
    ! [B_155,A_156,C_157] :
      ( k1_xboole_0 = B_155
      | k1_relset_1(A_156,B_155,C_157) = A_156
      | ~ v1_funct_2(C_157,A_156,B_155)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_364,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_361])).

tff(c_367,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_216,c_364])).

tff(c_368,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_367])).

tff(c_126,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_130,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_126])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_187,plain,(
    ! [C_87,B_88,A_89] :
      ( v5_relat_1(C_87,B_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_191,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_187])).

tff(c_253,plain,(
    ! [B_119,A_120] :
      ( r2_hidden(k1_funct_1(B_119,A_120),k2_relat_1(B_119))
      | ~ r2_hidden(A_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ! [C_46,A_43,B_44] :
      ( r2_hidden(C_46,A_43)
      | ~ r2_hidden(C_46,k2_relat_1(B_44))
      | ~ v5_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_292,plain,(
    ! [B_135,A_136,A_137] :
      ( r2_hidden(k1_funct_1(B_135,A_136),A_137)
      | ~ v5_relat_1(B_135,A_137)
      | ~ r2_hidden(A_136,k1_relat_1(B_135))
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_253,c_44])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_302,plain,(
    ! [B_138,A_139,A_140] :
      ( k1_funct_1(B_138,A_139) = A_140
      | ~ v5_relat_1(B_138,k1_tarski(A_140))
      | ~ r2_hidden(A_139,k1_relat_1(B_138))
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_292,c_14])).

tff(c_304,plain,(
    ! [A_139] :
      ( k1_funct_1('#skF_6',A_139) = '#skF_4'
      | ~ r2_hidden(A_139,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_191,c_302])).

tff(c_307,plain,(
    ! [A_139] :
      ( k1_funct_1('#skF_6',A_139) = '#skF_4'
      | ~ r2_hidden(A_139,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_76,c_304])).

tff(c_381,plain,(
    ! [A_158] :
      ( k1_funct_1('#skF_6',A_158) = '#skF_4'
      | ~ r2_hidden(A_158,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_307])).

tff(c_396,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_381])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:13:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.33  
% 2.70/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.70/1.33  
% 2.70/1.33  %Foreground sorts:
% 2.70/1.33  
% 2.70/1.33  
% 2.70/1.33  %Background operators:
% 2.70/1.33  
% 2.70/1.33  
% 2.70/1.33  %Foreground operators:
% 2.70/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.70/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.70/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.70/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.33  
% 2.70/1.35  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.70/1.35  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.70/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.35  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.70/1.35  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.70/1.35  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.70/1.35  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.70/1.35  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.70/1.35  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.70/1.35  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.70/1.35  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.70/1.35  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 2.70/1.35  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.70/1.35  tff(c_68, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.70/1.35  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.70/1.35  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.35  tff(c_111, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.35  tff(c_115, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_111])).
% 2.70/1.35  tff(c_131, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.35  tff(c_140, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_115, c_131])).
% 2.70/1.35  tff(c_143, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_140])).
% 2.70/1.35  tff(c_40, plain, (![B_42]: (k4_xboole_0(k1_tarski(B_42), k1_tarski(B_42))!=k1_tarski(B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.70/1.35  tff(c_144, plain, (![B_42]: (k1_tarski(B_42)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_40])).
% 2.70/1.35  tff(c_74, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.70/1.35  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.70/1.35  tff(c_212, plain, (![A_102, B_103, C_104]: (k1_relset_1(A_102, B_103, C_104)=k1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.70/1.35  tff(c_216, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_212])).
% 2.70/1.35  tff(c_361, plain, (![B_155, A_156, C_157]: (k1_xboole_0=B_155 | k1_relset_1(A_156, B_155, C_157)=A_156 | ~v1_funct_2(C_157, A_156, B_155) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.70/1.35  tff(c_364, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_361])).
% 2.70/1.35  tff(c_367, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_216, c_364])).
% 2.70/1.35  tff(c_368, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_144, c_367])).
% 2.70/1.35  tff(c_126, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.70/1.35  tff(c_130, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_126])).
% 2.70/1.35  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.70/1.35  tff(c_187, plain, (![C_87, B_88, A_89]: (v5_relat_1(C_87, B_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.70/1.35  tff(c_191, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_187])).
% 2.70/1.35  tff(c_253, plain, (![B_119, A_120]: (r2_hidden(k1_funct_1(B_119, A_120), k2_relat_1(B_119)) | ~r2_hidden(A_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.70/1.35  tff(c_44, plain, (![C_46, A_43, B_44]: (r2_hidden(C_46, A_43) | ~r2_hidden(C_46, k2_relat_1(B_44)) | ~v5_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.70/1.35  tff(c_292, plain, (![B_135, A_136, A_137]: (r2_hidden(k1_funct_1(B_135, A_136), A_137) | ~v5_relat_1(B_135, A_137) | ~r2_hidden(A_136, k1_relat_1(B_135)) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_253, c_44])).
% 2.70/1.35  tff(c_14, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.70/1.35  tff(c_302, plain, (![B_138, A_139, A_140]: (k1_funct_1(B_138, A_139)=A_140 | ~v5_relat_1(B_138, k1_tarski(A_140)) | ~r2_hidden(A_139, k1_relat_1(B_138)) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_292, c_14])).
% 2.70/1.35  tff(c_304, plain, (![A_139]: (k1_funct_1('#skF_6', A_139)='#skF_4' | ~r2_hidden(A_139, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_191, c_302])).
% 2.70/1.35  tff(c_307, plain, (![A_139]: (k1_funct_1('#skF_6', A_139)='#skF_4' | ~r2_hidden(A_139, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_76, c_304])).
% 2.70/1.35  tff(c_381, plain, (![A_158]: (k1_funct_1('#skF_6', A_158)='#skF_4' | ~r2_hidden(A_158, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_307])).
% 2.70/1.35  tff(c_396, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_70, c_381])).
% 2.70/1.35  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_396])).
% 2.70/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.35  
% 2.70/1.35  Inference rules
% 2.70/1.35  ----------------------
% 2.70/1.35  #Ref     : 0
% 2.70/1.35  #Sup     : 66
% 2.70/1.35  #Fact    : 0
% 2.70/1.35  #Define  : 0
% 2.70/1.35  #Split   : 0
% 2.70/1.35  #Chain   : 0
% 2.70/1.35  #Close   : 0
% 2.70/1.35  
% 2.70/1.35  Ordering : KBO
% 2.70/1.35  
% 2.70/1.35  Simplification rules
% 2.70/1.35  ----------------------
% 2.70/1.35  #Subsume      : 0
% 2.70/1.35  #Demod        : 22
% 2.70/1.35  #Tautology    : 43
% 2.70/1.35  #SimpNegUnit  : 5
% 2.70/1.35  #BackRed      : 5
% 2.70/1.35  
% 2.70/1.35  #Partial instantiations: 0
% 2.70/1.35  #Strategies tried      : 1
% 2.70/1.35  
% 2.70/1.35  Timing (in seconds)
% 2.70/1.35  ----------------------
% 2.70/1.35  Preprocessing        : 0.35
% 2.70/1.35  Parsing              : 0.18
% 2.70/1.35  CNF conversion       : 0.02
% 2.70/1.35  Main loop            : 0.25
% 2.70/1.35  Inferencing          : 0.09
% 2.70/1.35  Reduction            : 0.08
% 2.70/1.35  Demodulation         : 0.05
% 2.70/1.35  BG Simplification    : 0.02
% 2.70/1.35  Subsumption          : 0.05
% 2.70/1.35  Abstraction          : 0.02
% 2.70/1.35  MUC search           : 0.00
% 2.70/1.35  Cooper               : 0.00
% 2.70/1.35  Total                : 0.63
% 2.70/1.35  Index Insertion      : 0.00
% 2.70/1.35  Index Deletion       : 0.00
% 2.70/1.35  Index Matching       : 0.00
% 2.70/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
