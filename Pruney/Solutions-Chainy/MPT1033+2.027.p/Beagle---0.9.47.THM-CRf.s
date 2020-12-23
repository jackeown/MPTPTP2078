%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:54 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 148 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 486 expanded)
%              Number of equality atoms :   11 (  63 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( r2_relset_1(A_55,B_56,C_57,C_57)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_149,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_relset_1(A_62,B_63,C_64,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(resolution,[status(thm)],[c_16,c_130])).

tff(c_157,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_44,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_80,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_85,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_96,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_partfun1(C_49,A_50)
      | ~ v1_funct_2(C_49,A_50,B_51)
      | ~ v1_funct_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | v1_xboole_0(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_102,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_113,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_102])).

tff(c_114,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_113])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_99,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_109,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_99])).

tff(c_110,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_109])).

tff(c_32,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_160,plain,(
    ! [D_65,C_66,A_67,B_68] :
      ( D_65 = C_66
      | ~ r1_partfun1(C_66,D_65)
      | ~ v1_partfun1(D_65,A_67)
      | ~ v1_partfun1(C_66,A_67)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(D_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_162,plain,(
    ! [A_67,B_68] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_67)
      | ~ v1_partfun1('#skF_5',A_67)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_160])).

tff(c_165,plain,(
    ! [A_67,B_68] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_67)
      | ~ v1_partfun1('#skF_5',A_67)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_162])).

tff(c_284,plain,(
    ! [A_84,B_85] :
      ( ~ v1_partfun1('#skF_6',A_84)
      | ~ v1_partfun1('#skF_5',A_84)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_287,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_40,c_284])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_114,c_110,c_287])).

tff(c_292,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_296,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_28])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_296])).

tff(c_308,plain,(
    ! [A_86] : ~ r2_hidden(A_86,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_313,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_308])).

tff(c_307,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_78,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_44,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_318,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_318])).

tff(c_323,plain,(
    ! [A_88] : ~ r2_hidden(A_88,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_329,plain,(
    ! [B_89] : r1_tarski('#skF_5',B_89) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_354,plain,(
    ! [B_93] :
      ( B_93 = '#skF_5'
      | ~ r1_tarski(B_93,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_329,c_8])).

tff(c_369,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_313,c_354])).

tff(c_376,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_28])).

tff(c_401,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( r2_relset_1(A_95,B_96,C_97,C_97)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_423,plain,(
    ! [C_103] :
      ( r2_relset_1('#skF_3','#skF_4',C_103,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_401])).

tff(c_425,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_423])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:28:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.57  
% 2.80/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.58  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.80/1.58  
% 2.80/1.58  %Foreground sorts:
% 2.80/1.58  
% 2.80/1.58  
% 2.80/1.58  %Background operators:
% 2.80/1.58  
% 2.80/1.58  
% 2.80/1.58  %Foreground operators:
% 2.80/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.80/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.58  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.80/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.58  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.58  tff('#skF_6', type, '#skF_6': $i).
% 2.80/1.58  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.80/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.58  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.58  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.80/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.58  
% 2.80/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.80/1.59  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.80/1.59  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.80/1.59  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.80/1.59  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.80/1.59  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.80/1.59  tff(f_72, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.80/1.59  tff(f_89, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.80/1.59  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.59  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.80/1.59  tff(c_16, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.59  tff(c_130, plain, (![A_55, B_56, C_57, D_58]: (r2_relset_1(A_55, B_56, C_57, C_57) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.80/1.59  tff(c_149, plain, (![A_62, B_63, C_64]: (r2_relset_1(A_62, B_63, C_64, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(resolution, [status(thm)], [c_16, c_130])).
% 2.80/1.59  tff(c_157, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_149])).
% 2.80/1.59  tff(c_14, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.59  tff(c_69, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.80/1.59  tff(c_77, plain, (![A_44]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_44, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_69])).
% 2.80/1.59  tff(c_80, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_77])).
% 2.80/1.59  tff(c_85, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_14, c_80])).
% 2.80/1.59  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.80/1.59  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.80/1.59  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.80/1.59  tff(c_96, plain, (![C_49, A_50, B_51]: (v1_partfun1(C_49, A_50) | ~v1_funct_2(C_49, A_50, B_51) | ~v1_funct_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | v1_xboole_0(B_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.59  tff(c_102, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_96])).
% 2.80/1.59  tff(c_113, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_102])).
% 2.80/1.59  tff(c_114, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_85, c_113])).
% 2.80/1.59  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.80/1.59  tff(c_36, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.80/1.59  tff(c_99, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_96])).
% 2.80/1.59  tff(c_109, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_99])).
% 2.80/1.59  tff(c_110, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_85, c_109])).
% 2.80/1.59  tff(c_32, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.80/1.59  tff(c_160, plain, (![D_65, C_66, A_67, B_68]: (D_65=C_66 | ~r1_partfun1(C_66, D_65) | ~v1_partfun1(D_65, A_67) | ~v1_partfun1(C_66, A_67) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_1(D_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.80/1.59  tff(c_162, plain, (![A_67, B_68]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_67) | ~v1_partfun1('#skF_5', A_67) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_160])).
% 2.80/1.59  tff(c_165, plain, (![A_67, B_68]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_67) | ~v1_partfun1('#skF_5', A_67) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_162])).
% 2.80/1.59  tff(c_284, plain, (![A_84, B_85]: (~v1_partfun1('#skF_6', A_84) | ~v1_partfun1('#skF_5', A_84) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(splitLeft, [status(thm)], [c_165])).
% 2.80/1.59  tff(c_287, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_40, c_284])).
% 2.80/1.59  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_114, c_110, c_287])).
% 2.80/1.59  tff(c_292, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_165])).
% 2.80/1.59  tff(c_28, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.80/1.59  tff(c_296, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_292, c_28])).
% 2.80/1.59  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_296])).
% 2.80/1.59  tff(c_308, plain, (![A_86]: (~r2_hidden(A_86, '#skF_6'))), inference(splitRight, [status(thm)], [c_77])).
% 2.80/1.59  tff(c_313, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_308])).
% 2.80/1.59  tff(c_307, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_77])).
% 2.80/1.59  tff(c_78, plain, (![A_44]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_44, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_69])).
% 2.80/1.59  tff(c_318, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_78])).
% 2.80/1.59  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_318])).
% 2.80/1.59  tff(c_323, plain, (![A_88]: (~r2_hidden(A_88, '#skF_5'))), inference(splitRight, [status(thm)], [c_78])).
% 2.80/1.59  tff(c_329, plain, (![B_89]: (r1_tarski('#skF_5', B_89))), inference(resolution, [status(thm)], [c_6, c_323])).
% 2.80/1.59  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.59  tff(c_354, plain, (![B_93]: (B_93='#skF_5' | ~r1_tarski(B_93, '#skF_5'))), inference(resolution, [status(thm)], [c_329, c_8])).
% 2.80/1.59  tff(c_369, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_313, c_354])).
% 2.80/1.59  tff(c_376, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_28])).
% 2.80/1.59  tff(c_401, plain, (![A_95, B_96, C_97, D_98]: (r2_relset_1(A_95, B_96, C_97, C_97) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.80/1.59  tff(c_423, plain, (![C_103]: (r2_relset_1('#skF_3', '#skF_4', C_103, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_34, c_401])).
% 2.80/1.59  tff(c_425, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_423])).
% 2.80/1.59  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_425])).
% 2.80/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.59  
% 2.80/1.59  Inference rules
% 2.80/1.59  ----------------------
% 2.80/1.59  #Ref     : 0
% 2.80/1.59  #Sup     : 81
% 2.80/1.59  #Fact    : 0
% 2.80/1.59  #Define  : 0
% 2.80/1.59  #Split   : 6
% 2.80/1.59  #Chain   : 0
% 2.80/1.59  #Close   : 0
% 2.80/1.59  
% 2.80/1.59  Ordering : KBO
% 2.80/1.59  
% 2.80/1.59  Simplification rules
% 2.80/1.59  ----------------------
% 2.80/1.59  #Subsume      : 32
% 2.80/1.59  #Demod        : 44
% 2.80/1.59  #Tautology    : 21
% 2.80/1.59  #SimpNegUnit  : 3
% 2.80/1.59  #BackRed      : 15
% 2.80/1.59  
% 2.80/1.59  #Partial instantiations: 0
% 2.80/1.59  #Strategies tried      : 1
% 2.80/1.59  
% 2.80/1.59  Timing (in seconds)
% 2.80/1.59  ----------------------
% 2.80/1.60  Preprocessing        : 0.40
% 2.80/1.60  Parsing              : 0.22
% 2.80/1.60  CNF conversion       : 0.03
% 2.80/1.60  Main loop            : 0.27
% 2.80/1.60  Inferencing          : 0.10
% 2.80/1.60  Reduction            : 0.08
% 2.80/1.60  Demodulation         : 0.06
% 2.80/1.60  BG Simplification    : 0.02
% 2.80/1.60  Subsumption          : 0.05
% 2.80/1.60  Abstraction          : 0.01
% 2.80/1.60  MUC search           : 0.00
% 2.80/1.60  Cooper               : 0.00
% 2.80/1.60  Total                : 0.71
% 2.80/1.60  Index Insertion      : 0.00
% 2.80/1.60  Index Deletion       : 0.00
% 2.80/1.60  Index Matching       : 0.00
% 2.80/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
