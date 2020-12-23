%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:49 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 159 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 512 expanded)
%              Number of equality atoms :   33 ( 139 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_14,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( k1_relset_1(A_27,A_27,B_28) = A_27
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k2_zfmisc_1(A_27,A_27)))
      | ~ v1_funct_2(B_28,A_27,A_27)
      | ~ v1_funct_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_72,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_42,c_68])).

tff(c_73,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_42])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k1_relset_1(A_4,B_5,C_6),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_81,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_6])).

tff(c_85,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_4,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ r2_hidden(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_91,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_102,plain,(
    ! [D_37,C_38,B_39,A_40] :
      ( k1_funct_1(k2_funct_1(D_37),k1_funct_1(D_37,C_38)) = C_38
      | k1_xboole_0 = B_39
      | ~ r2_hidden(C_38,A_40)
      | ~ v2_funct_1(D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39)))
      | ~ v1_funct_2(D_37,A_40,B_39)
      | ~ v1_funct_1(D_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109,plain,(
    ! [D_41,B_42] :
      ( k1_funct_1(k2_funct_1(D_41),k1_funct_1(D_41,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_42
      | ~ v2_funct_1(D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_42)))
      | ~ v1_funct_2(D_41,'#skF_1',B_42)
      | ~ v1_funct_1(D_41) ) ),
    inference(resolution,[status(thm)],[c_18,c_102])).

tff(c_114,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_118,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_114])).

tff(c_119,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_122,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_122])).

tff(c_125,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_126,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_16,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_127,plain,(
    ! [D_43,B_44] :
      ( k1_funct_1(k2_funct_1(D_43),k1_funct_1(D_43,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_44
      | ~ v2_funct_1(D_43)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_44)))
      | ~ v1_funct_2(D_43,'#skF_1',B_44)
      | ~ v1_funct_1(D_43) ) ),
    inference(resolution,[status(thm)],[c_20,c_102])).

tff(c_132,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_136,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_16,c_132])).

tff(c_137,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_136])).

tff(c_142,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_137])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_142])).

tff(c_144,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_1') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.22  
% 2.13/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.22  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.13/1.22  
% 2.13/1.22  %Foreground sorts:
% 2.13/1.22  
% 2.13/1.22  
% 2.13/1.22  %Background operators:
% 2.13/1.22  
% 2.13/1.22  
% 2.13/1.22  %Foreground operators:
% 2.13/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.13/1.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.13/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.13/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.22  
% 2.13/1.24  tff(f_81, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.13/1.24  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.13/1.24  tff(f_63, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.13/1.24  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.13/1.24  tff(f_33, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.13/1.24  tff(f_55, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.13/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.13/1.24  tff(c_14, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.24  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.24  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.24  tff(c_26, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.24  tff(c_38, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.24  tff(c_42, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_38])).
% 2.13/1.24  tff(c_61, plain, (![A_27, B_28]: (k1_relset_1(A_27, A_27, B_28)=A_27 | ~m1_subset_1(B_28, k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))) | ~v1_funct_2(B_28, A_27, A_27) | ~v1_funct_1(B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.24  tff(c_68, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_61])).
% 2.13/1.24  tff(c_72, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_42, c_68])).
% 2.13/1.24  tff(c_73, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_42])).
% 2.13/1.24  tff(c_6, plain, (![A_4, B_5, C_6]: (m1_subset_1(k1_relset_1(A_4, B_5, C_6), k1_zfmisc_1(A_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.24  tff(c_81, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_73, c_6])).
% 2.13/1.24  tff(c_85, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_81])).
% 2.13/1.24  tff(c_4, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.24  tff(c_89, plain, (![A_1]: (~v1_xboole_0('#skF_1') | ~r2_hidden(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_85, c_4])).
% 2.13/1.24  tff(c_91, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_89])).
% 2.13/1.24  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.24  tff(c_18, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.24  tff(c_102, plain, (![D_37, C_38, B_39, A_40]: (k1_funct_1(k2_funct_1(D_37), k1_funct_1(D_37, C_38))=C_38 | k1_xboole_0=B_39 | ~r2_hidden(C_38, A_40) | ~v2_funct_1(D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))) | ~v1_funct_2(D_37, A_40, B_39) | ~v1_funct_1(D_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.24  tff(c_109, plain, (![D_41, B_42]: (k1_funct_1(k2_funct_1(D_41), k1_funct_1(D_41, '#skF_4'))='#skF_4' | k1_xboole_0=B_42 | ~v2_funct_1(D_41) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_42))) | ~v1_funct_2(D_41, '#skF_1', B_42) | ~v1_funct_1(D_41))), inference(resolution, [status(thm)], [c_18, c_102])).
% 2.13/1.24  tff(c_114, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_109])).
% 2.13/1.24  tff(c_118, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_114])).
% 2.13/1.24  tff(c_119, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_118])).
% 2.13/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.13/1.24  tff(c_122, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2])).
% 2.13/1.24  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_122])).
% 2.13/1.24  tff(c_125, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_118])).
% 2.13/1.24  tff(c_126, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_118])).
% 2.13/1.24  tff(c_16, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.24  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.24  tff(c_127, plain, (![D_43, B_44]: (k1_funct_1(k2_funct_1(D_43), k1_funct_1(D_43, '#skF_3'))='#skF_3' | k1_xboole_0=B_44 | ~v2_funct_1(D_43) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_44))) | ~v1_funct_2(D_43, '#skF_1', B_44) | ~v1_funct_1(D_43))), inference(resolution, [status(thm)], [c_20, c_102])).
% 2.13/1.24  tff(c_132, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_127])).
% 2.13/1.24  tff(c_136, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_16, c_132])).
% 2.13/1.24  tff(c_137, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_126, c_136])).
% 2.13/1.24  tff(c_142, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_137])).
% 2.13/1.24  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_142])).
% 2.13/1.24  tff(c_144, plain, (![A_1]: (~r2_hidden(A_1, '#skF_1'))), inference(splitRight, [status(thm)], [c_89])).
% 2.13/1.24  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_18])).
% 2.13/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  Inference rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Ref     : 0
% 2.13/1.24  #Sup     : 27
% 2.13/1.24  #Fact    : 0
% 2.13/1.24  #Define  : 0
% 2.13/1.24  #Split   : 3
% 2.13/1.24  #Chain   : 0
% 2.13/1.24  #Close   : 0
% 2.13/1.24  
% 2.13/1.24  Ordering : KBO
% 2.13/1.24  
% 2.13/1.24  Simplification rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Subsume      : 1
% 2.13/1.24  #Demod        : 20
% 2.13/1.24  #Tautology    : 11
% 2.13/1.24  #SimpNegUnit  : 5
% 2.13/1.24  #BackRed      : 6
% 2.13/1.24  
% 2.13/1.24  #Partial instantiations: 0
% 2.13/1.24  #Strategies tried      : 1
% 2.13/1.24  
% 2.13/1.24  Timing (in seconds)
% 2.13/1.24  ----------------------
% 2.13/1.24  Preprocessing        : 0.29
% 2.13/1.24  Parsing              : 0.16
% 2.13/1.24  CNF conversion       : 0.02
% 2.13/1.24  Main loop            : 0.17
% 2.13/1.24  Inferencing          : 0.06
% 2.13/1.24  Reduction            : 0.05
% 2.13/1.24  Demodulation         : 0.04
% 2.13/1.24  BG Simplification    : 0.01
% 2.13/1.24  Subsumption          : 0.02
% 2.13/1.24  Abstraction          : 0.01
% 2.13/1.24  MUC search           : 0.00
% 2.13/1.24  Cooper               : 0.00
% 2.13/1.24  Total                : 0.50
% 2.13/1.24  Index Insertion      : 0.00
% 2.13/1.24  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
