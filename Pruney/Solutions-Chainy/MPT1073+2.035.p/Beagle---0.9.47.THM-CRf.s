%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:02 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 128 expanded)
%              Number of leaves         :   33 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 279 expanded)
%              Number of equality atoms :   22 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_97,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_111,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_97])).

tff(c_62,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(B_34)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [E_27] :
      ( k1_funct_1('#skF_6',E_27) != '#skF_3'
      | ~ m1_subset_1(E_27,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_71,plain,(
    ! [B_34] :
      ( k1_funct_1('#skF_6',B_34) != '#skF_3'
      | ~ v1_xboole_0(B_34)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_36])).

tff(c_113,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_207,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k7_relset_1(A_75,B_76,C_77,D_78) = k9_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_220,plain,(
    ! [D_78] : k7_relset_1('#skF_4','#skF_5','#skF_6',D_78) = k9_relat_1('#skF_6',D_78) ),
    inference(resolution,[status(thm)],[c_40,c_207])).

tff(c_333,plain,(
    ! [A_96,B_97,C_98] :
      ( k7_relset_1(A_96,B_97,C_98,A_96) = k2_relset_1(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_341,plain,(
    k7_relset_1('#skF_4','#skF_5','#skF_6','#skF_4') = k2_relset_1('#skF_4','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_333])).

tff(c_347,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k9_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_341])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_350,plain,(
    r2_hidden('#skF_3',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_38])).

tff(c_133,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_2'(A_51,B_52,C_53),B_52)
      | ~ r2_hidden(A_51,k9_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_656,plain,(
    ! [A_137,B_138,C_139] :
      ( m1_subset_1('#skF_2'(A_137,B_138,C_139),B_138)
      | v1_xboole_0(B_138)
      | ~ r2_hidden(A_137,k9_relat_1(C_139,B_138))
      | ~ v1_relat_1(C_139) ) ),
    inference(resolution,[status(thm)],[c_133,c_6])).

tff(c_663,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_350,c_656])).

tff(c_682,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_663])).

tff(c_683,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_682])).

tff(c_695,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_683,c_36])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_453,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_hidden(k4_tarski('#skF_2'(A_110,B_111,C_112),A_110),C_112)
      | ~ r2_hidden(A_110,k9_relat_1(C_112,B_111))
      | ~ v1_relat_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [C_15,A_13,B_14] :
      ( k1_funct_1(C_15,A_13) = B_14
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_728,plain,(
    ! [C_147,A_148,B_149] :
      ( k1_funct_1(C_147,'#skF_2'(A_148,B_149,C_147)) = A_148
      | ~ v1_funct_1(C_147)
      | ~ r2_hidden(A_148,k9_relat_1(C_147,B_149))
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_453,c_24])).

tff(c_735,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_350,c_728])).

tff(c_752,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_44,c_735])).

tff(c_754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_695,c_752])).

tff(c_756,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_781,plain,(
    ! [A_160,B_161,C_162] :
      ( r2_hidden('#skF_2'(A_160,B_161,C_162),B_161)
      | ~ r2_hidden(A_160,k9_relat_1(C_162,B_161))
      | ~ v1_relat_1(C_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_796,plain,(
    ! [B_166,A_167,C_168] :
      ( ~ v1_xboole_0(B_166)
      | ~ r2_hidden(A_167,k9_relat_1(C_168,B_166))
      | ~ v1_relat_1(C_168) ) ),
    inference(resolution,[status(thm)],[c_781,c_2])).

tff(c_811,plain,(
    ! [B_166,C_168] :
      ( ~ v1_xboole_0(B_166)
      | ~ v1_relat_1(C_168)
      | v1_xboole_0(k9_relat_1(C_168,B_166)) ) ),
    inference(resolution,[status(thm)],[c_4,c_796])).

tff(c_818,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( k7_relset_1(A_173,B_174,C_175,D_176) = k9_relat_1(C_175,D_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_831,plain,(
    ! [D_176] : k7_relset_1('#skF_4','#skF_5','#skF_6',D_176) = k9_relat_1('#skF_6',D_176) ),
    inference(resolution,[status(thm)],[c_40,c_818])).

tff(c_871,plain,(
    ! [A_188,B_189,C_190] :
      ( k7_relset_1(A_188,B_189,C_190,A_188) = k2_relset_1(A_188,B_189,C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_879,plain,(
    k7_relset_1('#skF_4','#skF_5','#skF_6','#skF_4') = k2_relset_1('#skF_4','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_871])).

tff(c_885,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k9_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_879])).

tff(c_49,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_887,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_49])).

tff(c_895,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_811,c_887])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_756,c_895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.43  
% 2.95/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.43  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.95/1.43  
% 2.95/1.43  %Foreground sorts:
% 2.95/1.43  
% 2.95/1.43  
% 2.95/1.43  %Background operators:
% 2.95/1.43  
% 2.95/1.43  
% 2.95/1.43  %Foreground operators:
% 2.95/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.95/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.95/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.95/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.95/1.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.95/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.95/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.95/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.95/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.95/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.95/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.43  
% 2.95/1.45  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.95/1.45  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.95/1.45  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.95/1.45  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.95/1.45  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.95/1.45  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.95/1.45  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.95/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.95/1.45  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.95/1.45  tff(c_97, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.95/1.45  tff(c_111, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_97])).
% 2.95/1.45  tff(c_62, plain, (![B_34, A_35]: (m1_subset_1(B_34, A_35) | ~v1_xboole_0(B_34) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.45  tff(c_36, plain, (![E_27]: (k1_funct_1('#skF_6', E_27)!='#skF_3' | ~m1_subset_1(E_27, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.95/1.45  tff(c_71, plain, (![B_34]: (k1_funct_1('#skF_6', B_34)!='#skF_3' | ~v1_xboole_0(B_34) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_36])).
% 2.95/1.45  tff(c_113, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_71])).
% 2.95/1.45  tff(c_207, plain, (![A_75, B_76, C_77, D_78]: (k7_relset_1(A_75, B_76, C_77, D_78)=k9_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.95/1.45  tff(c_220, plain, (![D_78]: (k7_relset_1('#skF_4', '#skF_5', '#skF_6', D_78)=k9_relat_1('#skF_6', D_78))), inference(resolution, [status(thm)], [c_40, c_207])).
% 2.95/1.45  tff(c_333, plain, (![A_96, B_97, C_98]: (k7_relset_1(A_96, B_97, C_98, A_96)=k2_relset_1(A_96, B_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.45  tff(c_341, plain, (k7_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_4')=k2_relset_1('#skF_4', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_333])).
% 2.95/1.45  tff(c_347, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k9_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_341])).
% 2.95/1.45  tff(c_38, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.95/1.45  tff(c_350, plain, (r2_hidden('#skF_3', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_38])).
% 2.95/1.45  tff(c_133, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_2'(A_51, B_52, C_53), B_52) | ~r2_hidden(A_51, k9_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.95/1.45  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.95/1.45  tff(c_656, plain, (![A_137, B_138, C_139]: (m1_subset_1('#skF_2'(A_137, B_138, C_139), B_138) | v1_xboole_0(B_138) | ~r2_hidden(A_137, k9_relat_1(C_139, B_138)) | ~v1_relat_1(C_139))), inference(resolution, [status(thm)], [c_133, c_6])).
% 2.95/1.45  tff(c_663, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4') | v1_xboole_0('#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_350, c_656])).
% 2.95/1.45  tff(c_682, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_663])).
% 2.95/1.45  tff(c_683, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_113, c_682])).
% 2.95/1.45  tff(c_695, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3'), inference(resolution, [status(thm)], [c_683, c_36])).
% 2.95/1.45  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.95/1.45  tff(c_453, plain, (![A_110, B_111, C_112]: (r2_hidden(k4_tarski('#skF_2'(A_110, B_111, C_112), A_110), C_112) | ~r2_hidden(A_110, k9_relat_1(C_112, B_111)) | ~v1_relat_1(C_112))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.95/1.45  tff(c_24, plain, (![C_15, A_13, B_14]: (k1_funct_1(C_15, A_13)=B_14 | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.45  tff(c_728, plain, (![C_147, A_148, B_149]: (k1_funct_1(C_147, '#skF_2'(A_148, B_149, C_147))=A_148 | ~v1_funct_1(C_147) | ~r2_hidden(A_148, k9_relat_1(C_147, B_149)) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_453, c_24])).
% 2.95/1.45  tff(c_735, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_350, c_728])).
% 2.95/1.45  tff(c_752, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_44, c_735])).
% 2.95/1.45  tff(c_754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_695, c_752])).
% 2.95/1.45  tff(c_756, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_71])).
% 2.95/1.45  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.45  tff(c_781, plain, (![A_160, B_161, C_162]: (r2_hidden('#skF_2'(A_160, B_161, C_162), B_161) | ~r2_hidden(A_160, k9_relat_1(C_162, B_161)) | ~v1_relat_1(C_162))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.95/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.45  tff(c_796, plain, (![B_166, A_167, C_168]: (~v1_xboole_0(B_166) | ~r2_hidden(A_167, k9_relat_1(C_168, B_166)) | ~v1_relat_1(C_168))), inference(resolution, [status(thm)], [c_781, c_2])).
% 2.95/1.45  tff(c_811, plain, (![B_166, C_168]: (~v1_xboole_0(B_166) | ~v1_relat_1(C_168) | v1_xboole_0(k9_relat_1(C_168, B_166)))), inference(resolution, [status(thm)], [c_4, c_796])).
% 2.95/1.45  tff(c_818, plain, (![A_173, B_174, C_175, D_176]: (k7_relset_1(A_173, B_174, C_175, D_176)=k9_relat_1(C_175, D_176) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.95/1.45  tff(c_831, plain, (![D_176]: (k7_relset_1('#skF_4', '#skF_5', '#skF_6', D_176)=k9_relat_1('#skF_6', D_176))), inference(resolution, [status(thm)], [c_40, c_818])).
% 2.95/1.45  tff(c_871, plain, (![A_188, B_189, C_190]: (k7_relset_1(A_188, B_189, C_190, A_188)=k2_relset_1(A_188, B_189, C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.45  tff(c_879, plain, (k7_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_4')=k2_relset_1('#skF_4', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_871])).
% 2.95/1.45  tff(c_885, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k9_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_831, c_879])).
% 2.95/1.45  tff(c_49, plain, (~v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_2])).
% 2.95/1.45  tff(c_887, plain, (~v1_xboole_0(k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_49])).
% 2.95/1.45  tff(c_895, plain, (~v1_xboole_0('#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_811, c_887])).
% 2.95/1.45  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_756, c_895])).
% 2.95/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.45  
% 2.95/1.45  Inference rules
% 2.95/1.45  ----------------------
% 2.95/1.45  #Ref     : 0
% 2.95/1.45  #Sup     : 172
% 2.95/1.45  #Fact    : 0
% 2.95/1.45  #Define  : 0
% 2.95/1.45  #Split   : 5
% 2.95/1.45  #Chain   : 0
% 2.95/1.45  #Close   : 0
% 2.95/1.45  
% 2.95/1.45  Ordering : KBO
% 2.95/1.45  
% 2.95/1.45  Simplification rules
% 2.95/1.45  ----------------------
% 2.95/1.45  #Subsume      : 33
% 2.95/1.45  #Demod        : 29
% 2.95/1.45  #Tautology    : 22
% 2.95/1.45  #SimpNegUnit  : 12
% 2.95/1.45  #BackRed      : 6
% 2.95/1.45  
% 2.95/1.45  #Partial instantiations: 0
% 2.95/1.45  #Strategies tried      : 1
% 2.95/1.45  
% 2.95/1.45  Timing (in seconds)
% 2.95/1.45  ----------------------
% 2.95/1.45  Preprocessing        : 0.31
% 2.95/1.45  Parsing              : 0.16
% 2.95/1.45  CNF conversion       : 0.02
% 2.95/1.45  Main loop            : 0.38
% 2.95/1.45  Inferencing          : 0.15
% 2.95/1.45  Reduction            : 0.09
% 2.95/1.45  Demodulation         : 0.06
% 2.95/1.45  BG Simplification    : 0.02
% 2.95/1.45  Subsumption          : 0.09
% 2.95/1.45  Abstraction          : 0.02
% 2.95/1.45  MUC search           : 0.00
% 2.95/1.45  Cooper               : 0.00
% 2.95/1.45  Total                : 0.72
% 2.95/1.45  Index Insertion      : 0.00
% 2.95/1.45  Index Deletion       : 0.00
% 2.95/1.45  Index Matching       : 0.00
% 2.95/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
