%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:32 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 160 expanded)
%              Number of leaves         :   38 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 373 expanded)
%              Number of equality atoms :   33 ( 110 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_114,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_114])).

tff(c_120,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    ! [A_10,C_46] :
      ( k1_funct_1(A_10,'#skF_4'(A_10,k2_relat_1(A_10),C_46)) = C_46
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_154,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_164,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_154])).

tff(c_252,plain,(
    ! [B_128,A_129,C_130] :
      ( k1_xboole_0 = B_128
      | k1_relset_1(A_129,B_128,C_130) = A_129
      | ~ v1_funct_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_255,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_252])).

tff(c_264,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_164,c_255])).

tff(c_266,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_20,plain,(
    ! [A_10,C_46] :
      ( r2_hidden('#skF_4'(A_10,k2_relat_1(A_10),C_46),k1_relat_1(A_10))
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_274,plain,(
    ! [C_46] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_46),'#skF_5')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_20])).

tff(c_287,plain,(
    ! [C_132] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_132),'#skF_5')
      | ~ r2_hidden(C_132,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_64,c_274])).

tff(c_56,plain,(
    ! [E_65] :
      ( k1_funct_1('#skF_8',E_65) != '#skF_7'
      | ~ r2_hidden(E_65,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_296,plain,(
    ! [C_133] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_133)) != '#skF_7'
      | ~ r2_hidden(C_133,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_287,c_56])).

tff(c_300,plain,(
    ! [C_46] :
      ( C_46 != '#skF_7'
      | ~ r2_hidden(C_46,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_46,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_296])).

tff(c_303,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_64,c_300])).

tff(c_170,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_180,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_170])).

tff(c_58,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_182,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_58])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_182])).

tff(c_306,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_331,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_306,c_4])).

tff(c_339,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_60])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_144,plain,(
    ! [C_85,B_2] :
      ( v5_relat_1(C_85,B_2)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_415,plain,(
    ! [C_144,B_145] :
      ( v5_relat_1(C_144,B_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_144])).

tff(c_418,plain,(
    ! [B_145] : v5_relat_1('#skF_8',B_145) ),
    inference(resolution,[status(thm)],[c_339,c_415])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [B_51,A_50] :
      ( ~ r1_tarski(B_51,A_50)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,(
    ~ r1_tarski(k2_relset_1('#skF_5','#skF_6','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_34])).

tff(c_181,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_101])).

tff(c_189,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_181])).

tff(c_192,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_189])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:19:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.96  
% 2.96/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.96/1.96  
% 2.96/1.96  %Foreground sorts:
% 2.96/1.96  
% 2.96/1.96  
% 2.96/1.96  %Background operators:
% 2.96/1.96  
% 2.96/1.96  
% 2.96/1.96  %Foreground operators:
% 2.96/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.96/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.96/1.96  tff('#skF_7', type, '#skF_7': $i).
% 2.96/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.96/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.96/1.96  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.96/1.96  tff('#skF_6', type, '#skF_6': $i).
% 2.96/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.96/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.96/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.96/1.96  tff('#skF_8', type, '#skF_8': $i).
% 2.96/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.96/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.96/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.96  
% 2.96/1.98  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.96/1.98  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.96/1.98  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.96/1.98  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.96/1.98  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.96/1.98  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.96/1.98  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.96/1.98  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.96/1.98  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.96/1.98  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.96/1.98  tff(f_66, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.96/1.98  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.96/1.98  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.96/1.98  tff(c_114, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.98  tff(c_117, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_114])).
% 2.96/1.98  tff(c_120, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_117])).
% 2.96/1.98  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.96/1.98  tff(c_18, plain, (![A_10, C_46]: (k1_funct_1(A_10, '#skF_4'(A_10, k2_relat_1(A_10), C_46))=C_46 | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.98  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.96/1.98  tff(c_154, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.96/1.98  tff(c_164, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_154])).
% 2.96/1.98  tff(c_252, plain, (![B_128, A_129, C_130]: (k1_xboole_0=B_128 | k1_relset_1(A_129, B_128, C_130)=A_129 | ~v1_funct_2(C_130, A_129, B_128) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.96/1.98  tff(c_255, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_252])).
% 2.96/1.98  tff(c_264, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_164, c_255])).
% 2.96/1.98  tff(c_266, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_264])).
% 2.96/1.98  tff(c_20, plain, (![A_10, C_46]: (r2_hidden('#skF_4'(A_10, k2_relat_1(A_10), C_46), k1_relat_1(A_10)) | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.98  tff(c_274, plain, (![C_46]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_46), '#skF_5') | ~r2_hidden(C_46, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_20])).
% 2.96/1.98  tff(c_287, plain, (![C_132]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_132), '#skF_5') | ~r2_hidden(C_132, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_64, c_274])).
% 2.96/1.98  tff(c_56, plain, (![E_65]: (k1_funct_1('#skF_8', E_65)!='#skF_7' | ~r2_hidden(E_65, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.96/1.98  tff(c_296, plain, (![C_133]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_133))!='#skF_7' | ~r2_hidden(C_133, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_287, c_56])).
% 2.96/1.98  tff(c_300, plain, (![C_46]: (C_46!='#skF_7' | ~r2_hidden(C_46, k2_relat_1('#skF_8')) | ~r2_hidden(C_46, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_296])).
% 2.96/1.98  tff(c_303, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_64, c_300])).
% 2.96/1.98  tff(c_170, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.98  tff(c_180, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_170])).
% 2.96/1.98  tff(c_58, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.96/1.98  tff(c_182, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_58])).
% 2.96/1.98  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_182])).
% 2.96/1.98  tff(c_306, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_264])).
% 2.96/1.98  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.98  tff(c_331, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_306, c_4])).
% 2.96/1.98  tff(c_339, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_60])).
% 2.96/1.98  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.98  tff(c_135, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.96/1.98  tff(c_144, plain, (![C_85, B_2]: (v5_relat_1(C_85, B_2) | ~m1_subset_1(C_85, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_135])).
% 2.96/1.98  tff(c_415, plain, (![C_144, B_145]: (v5_relat_1(C_144, B_145) | ~m1_subset_1(C_144, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_144])).
% 2.96/1.98  tff(c_418, plain, (![B_145]: (v5_relat_1('#skF_8', B_145))), inference(resolution, [status(thm)], [c_339, c_415])).
% 2.96/1.98  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.96/1.98  tff(c_34, plain, (![B_51, A_50]: (~r1_tarski(B_51, A_50) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.96/1.98  tff(c_101, plain, (~r1_tarski(k2_relset_1('#skF_5', '#skF_6', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_58, c_34])).
% 2.96/1.98  tff(c_181, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_101])).
% 2.96/1.98  tff(c_189, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_181])).
% 2.96/1.98  tff(c_192, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_189])).
% 2.96/1.98  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_418, c_192])).
% 2.96/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.98  
% 2.96/1.98  Inference rules
% 2.96/1.98  ----------------------
% 2.96/1.98  #Ref     : 0
% 2.96/1.98  #Sup     : 79
% 2.96/1.98  #Fact    : 0
% 2.96/1.98  #Define  : 0
% 2.96/1.98  #Split   : 2
% 2.96/1.98  #Chain   : 0
% 2.96/1.98  #Close   : 0
% 2.96/1.98  
% 2.96/1.98  Ordering : KBO
% 2.96/1.98  
% 2.96/1.98  Simplification rules
% 2.96/1.98  ----------------------
% 2.96/1.98  #Subsume      : 7
% 2.96/1.98  #Demod        : 62
% 2.96/1.98  #Tautology    : 37
% 2.96/1.98  #SimpNegUnit  : 1
% 2.96/1.98  #BackRed      : 22
% 2.96/1.98  
% 2.96/1.98  #Partial instantiations: 0
% 2.96/1.98  #Strategies tried      : 1
% 2.96/1.98  
% 2.96/1.98  Timing (in seconds)
% 2.96/1.98  ----------------------
% 3.09/1.98  Preprocessing        : 0.67
% 3.09/1.98  Parsing              : 0.36
% 3.09/1.98  CNF conversion       : 0.05
% 3.09/1.98  Main loop            : 0.38
% 3.09/1.98  Inferencing          : 0.12
% 3.09/1.98  Reduction            : 0.12
% 3.09/1.98  Demodulation         : 0.09
% 3.09/1.98  BG Simplification    : 0.04
% 3.09/1.98  Subsumption          : 0.08
% 3.09/1.98  Abstraction          : 0.03
% 3.09/1.98  MUC search           : 0.00
% 3.09/1.98  Cooper               : 0.00
% 3.09/1.98  Total                : 1.10
% 3.09/1.98  Index Insertion      : 0.00
% 3.09/1.98  Index Deletion       : 0.00
% 3.09/1.98  Index Matching       : 0.00
% 3.09/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
