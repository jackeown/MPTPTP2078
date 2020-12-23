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
% DateTime   : Thu Dec  3 10:11:26 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 161 expanded)
%              Number of leaves         :   32 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 441 expanded)
%              Number of equality atoms :   30 ( 109 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_137,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_141,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_137])).

tff(c_32,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_142,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_32])).

tff(c_22,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68])).

tff(c_132,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_203,plain,(
    ! [D_81,C_82,A_83,B_84] :
      ( r2_hidden(k1_funct_1(D_81,C_82),k2_relset_1(A_83,B_84,D_81))
      | k1_xboole_0 = B_84
      | ~ r2_hidden(C_82,A_83)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(D_81,A_83,B_84)
      | ~ v1_funct_1(D_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_208,plain,(
    ! [C_82] :
      ( r2_hidden(k1_funct_1('#skF_4',C_82),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_82,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_203])).

tff(c_214,plain,(
    ! [C_82] :
      ( r2_hidden(k1_funct_1('#skF_4',C_82),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_82,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_208])).

tff(c_268,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_102,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(k2_relat_1(B_49),A_50)
      | ~ v5_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_109,plain,(
    ! [B_49] :
      ( k2_relat_1(B_49) = k1_xboole_0
      | ~ v5_relat_1(B_49,k1_xboole_0)
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_102,c_77])).

tff(c_341,plain,(
    ! [B_103] :
      ( k2_relat_1(B_103) = '#skF_3'
      | ~ v5_relat_1(B_103,'#skF_3')
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_268,c_109])).

tff(c_344,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_341])).

tff(c_347,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_344])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_347])).

tff(c_351,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_42,plain,(
    ! [D_29] :
      ( r2_hidden('#skF_5'(D_29),'#skF_2')
      | ~ r2_hidden(D_29,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [D_29] :
      ( k1_funct_1('#skF_4','#skF_5'(D_29)) = D_29
      | ~ r2_hidden(D_29,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_211,plain,(
    ! [D_29,A_83,B_84] :
      ( r2_hidden(D_29,k2_relset_1(A_83,B_84,'#skF_4'))
      | k1_xboole_0 = B_84
      | ~ r2_hidden('#skF_5'(D_29),A_83)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2('#skF_4',A_83,B_84)
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(D_29,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_203])).

tff(c_261,plain,(
    ! [D_91,A_92,B_93] :
      ( r2_hidden(D_91,k2_relset_1(A_92,B_93,'#skF_4'))
      | k1_xboole_0 = B_93
      | ~ r2_hidden('#skF_5'(D_91),A_92)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2('#skF_4',A_92,B_93)
      | ~ r2_hidden(D_91,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_211])).

tff(c_352,plain,(
    ! [D_104,B_105] :
      ( r2_hidden(D_104,k2_relset_1('#skF_2',B_105,'#skF_4'))
      | k1_xboole_0 = B_105
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_105)))
      | ~ v1_funct_2('#skF_4','#skF_2',B_105)
      | ~ r2_hidden(D_104,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_261])).

tff(c_354,plain,(
    ! [D_104] :
      ( r2_hidden(D_104,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ r2_hidden(D_104,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_352])).

tff(c_357,plain,(
    ! [D_104] :
      ( r2_hidden(D_104,k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(D_104,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_141,c_354])).

tff(c_366,plain,(
    ! [D_107] :
      ( r2_hidden(D_107,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_107,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_357])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_420,plain,(
    ! [A_117] :
      ( r1_tarski(A_117,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_117,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_366,c_4])).

tff(c_430,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_420])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [B_49,A_50] :
      ( k2_relat_1(B_49) = A_50
      | ~ r1_tarski(A_50,k2_relat_1(B_49))
      | ~ v5_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_435,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_430,c_110])).

tff(c_443,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_136,c_435])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.78/1.45  
% 2.78/1.45  %Foreground sorts:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Background operators:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Foreground operators:
% 2.78/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.45  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.78/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.45  
% 2.91/1.46  tff(f_96, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 2.91/1.46  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.91/1.46  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.91/1.46  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.91/1.46  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.91/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.91/1.46  tff(f_77, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.91/1.46  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.91/1.46  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.91/1.46  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.91/1.46  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.46  tff(c_137, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.91/1.46  tff(c_141, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_137])).
% 2.91/1.46  tff(c_32, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.46  tff(c_142, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_32])).
% 2.91/1.46  tff(c_22, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.91/1.46  tff(c_65, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.46  tff(c_68, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.91/1.46  tff(c_71, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_68])).
% 2.91/1.46  tff(c_132, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.91/1.46  tff(c_136, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_132])).
% 2.91/1.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.46  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.46  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.46  tff(c_203, plain, (![D_81, C_82, A_83, B_84]: (r2_hidden(k1_funct_1(D_81, C_82), k2_relset_1(A_83, B_84, D_81)) | k1_xboole_0=B_84 | ~r2_hidden(C_82, A_83) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(D_81, A_83, B_84) | ~v1_funct_1(D_81))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.91/1.46  tff(c_208, plain, (![C_82]: (r2_hidden(k1_funct_1('#skF_4', C_82), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_82, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_203])).
% 2.91/1.46  tff(c_214, plain, (![C_82]: (r2_hidden(k1_funct_1('#skF_4', C_82), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_82, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_208])).
% 2.91/1.46  tff(c_268, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_214])).
% 2.91/1.46  tff(c_102, plain, (![B_49, A_50]: (r1_tarski(k2_relat_1(B_49), A_50) | ~v5_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.91/1.46  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.91/1.46  tff(c_72, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.91/1.46  tff(c_77, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_72])).
% 2.91/1.46  tff(c_109, plain, (![B_49]: (k2_relat_1(B_49)=k1_xboole_0 | ~v5_relat_1(B_49, k1_xboole_0) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_102, c_77])).
% 2.91/1.46  tff(c_341, plain, (![B_103]: (k2_relat_1(B_103)='#skF_3' | ~v5_relat_1(B_103, '#skF_3') | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_268, c_109])).
% 2.91/1.46  tff(c_344, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_136, c_341])).
% 2.91/1.46  tff(c_347, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_344])).
% 2.91/1.46  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_347])).
% 2.91/1.46  tff(c_351, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_214])).
% 2.91/1.46  tff(c_42, plain, (![D_29]: (r2_hidden('#skF_5'(D_29), '#skF_2') | ~r2_hidden(D_29, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.46  tff(c_40, plain, (![D_29]: (k1_funct_1('#skF_4', '#skF_5'(D_29))=D_29 | ~r2_hidden(D_29, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.46  tff(c_211, plain, (![D_29, A_83, B_84]: (r2_hidden(D_29, k2_relset_1(A_83, B_84, '#skF_4')) | k1_xboole_0=B_84 | ~r2_hidden('#skF_5'(D_29), A_83) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2('#skF_4', A_83, B_84) | ~v1_funct_1('#skF_4') | ~r2_hidden(D_29, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_203])).
% 2.91/1.46  tff(c_261, plain, (![D_91, A_92, B_93]: (r2_hidden(D_91, k2_relset_1(A_92, B_93, '#skF_4')) | k1_xboole_0=B_93 | ~r2_hidden('#skF_5'(D_91), A_92) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_2('#skF_4', A_92, B_93) | ~r2_hidden(D_91, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_211])).
% 2.91/1.46  tff(c_352, plain, (![D_104, B_105]: (r2_hidden(D_104, k2_relset_1('#skF_2', B_105, '#skF_4')) | k1_xboole_0=B_105 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_105))) | ~v1_funct_2('#skF_4', '#skF_2', B_105) | ~r2_hidden(D_104, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_261])).
% 2.91/1.46  tff(c_354, plain, (![D_104]: (r2_hidden(D_104, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~r2_hidden(D_104, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_352])).
% 2.91/1.46  tff(c_357, plain, (![D_104]: (r2_hidden(D_104, k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(D_104, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_141, c_354])).
% 2.91/1.46  tff(c_366, plain, (![D_107]: (r2_hidden(D_107, k2_relat_1('#skF_4')) | ~r2_hidden(D_107, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_351, c_357])).
% 2.91/1.46  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.46  tff(c_420, plain, (![A_117]: (r1_tarski(A_117, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_117, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_366, c_4])).
% 2.91/1.46  tff(c_430, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_420])).
% 2.91/1.46  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.91/1.46  tff(c_110, plain, (![B_49, A_50]: (k2_relat_1(B_49)=A_50 | ~r1_tarski(A_50, k2_relat_1(B_49)) | ~v5_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_102, c_8])).
% 2.91/1.46  tff(c_435, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_430, c_110])).
% 2.91/1.46  tff(c_443, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_136, c_435])).
% 2.91/1.46  tff(c_445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_443])).
% 2.91/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.46  
% 2.91/1.46  Inference rules
% 2.91/1.46  ----------------------
% 2.91/1.46  #Ref     : 0
% 2.91/1.46  #Sup     : 83
% 2.91/1.46  #Fact    : 0
% 2.91/1.46  #Define  : 0
% 2.91/1.46  #Split   : 3
% 2.91/1.46  #Chain   : 0
% 2.91/1.46  #Close   : 0
% 2.91/1.46  
% 2.91/1.46  Ordering : KBO
% 2.91/1.46  
% 2.91/1.46  Simplification rules
% 2.91/1.46  ----------------------
% 2.91/1.46  #Subsume      : 11
% 2.91/1.46  #Demod        : 38
% 2.91/1.46  #Tautology    : 21
% 2.91/1.46  #SimpNegUnit  : 4
% 2.91/1.46  #BackRed      : 10
% 2.91/1.46  
% 2.91/1.46  #Partial instantiations: 0
% 2.91/1.46  #Strategies tried      : 1
% 2.91/1.46  
% 2.91/1.46  Timing (in seconds)
% 2.91/1.46  ----------------------
% 2.91/1.47  Preprocessing        : 0.34
% 2.91/1.47  Parsing              : 0.18
% 2.91/1.47  CNF conversion       : 0.02
% 2.91/1.47  Main loop            : 0.30
% 2.91/1.47  Inferencing          : 0.11
% 2.91/1.47  Reduction            : 0.08
% 2.91/1.47  Demodulation         : 0.06
% 2.91/1.47  BG Simplification    : 0.02
% 2.91/1.47  Subsumption          : 0.07
% 2.91/1.47  Abstraction          : 0.02
% 2.91/1.47  MUC search           : 0.00
% 2.91/1.47  Cooper               : 0.00
% 2.91/1.47  Total                : 0.68
% 2.91/1.47  Index Insertion      : 0.00
% 2.91/1.47  Index Deletion       : 0.00
% 2.91/1.47  Index Matching       : 0.00
% 2.91/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
