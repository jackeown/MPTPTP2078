%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:20 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 135 expanded)
%              Number of leaves         :   29 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 277 expanded)
%              Number of equality atoms :   22 (  68 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_110,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_119,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_110])).

tff(c_26,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_120,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_26])).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_90])).

tff(c_96,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_125,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_134,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_146,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k2_relset_1(A_54,B_55,C_56),k1_zfmisc_1(B_55))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_160,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_146])).

tff(c_165,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_160])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1('#skF_1'(A_2,B_3),A_2)
      | k1_xboole_0 = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),B_44)
      | k1_xboole_0 = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [D_32] :
      ( ~ r2_hidden(D_32,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_32,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_103,plain,(
    ! [A_43] :
      ( ~ m1_subset_1('#skF_1'(A_43,k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
      | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_98,c_24])).

tff(c_187,plain,(
    ! [A_43] :
      ( ~ m1_subset_1('#skF_1'(A_43,k2_relat_1('#skF_4')),'#skF_3')
      | k2_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_43)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_134,c_134,c_103])).

tff(c_189,plain,(
    ! [A_60] :
      ( ~ m1_subset_1('#skF_1'(A_60,k2_relat_1('#skF_4')),'#skF_3')
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_60)) ) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_193,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_189])).

tff(c_196,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_193])).

tff(c_16,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(k2_relat_1(A_11))
      | ~ v1_relat_1(A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_204,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_16])).

tff(c_208,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2,c_204])).

tff(c_40,plain,(
    ! [A_36] :
      ( v1_xboole_0(k1_relat_1(A_36))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_44,plain,(
    ! [A_36] :
      ( k1_relat_1(A_36) = k1_xboole_0
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_40,c_4])).

tff(c_212,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_208,c_44])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_212])).

tff(c_220,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_227,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_16])).

tff(c_231,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2,c_227])).

tff(c_235,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_231,c_44])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:57:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.27  
% 2.24/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.27  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.24/1.27  
% 2.24/1.27  %Foreground sorts:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Background operators:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Foreground operators:
% 2.24/1.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.27  
% 2.24/1.29  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.24/1.29  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.24/1.29  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.24/1.29  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.24/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.24/1.29  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.24/1.29  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.24/1.29  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 2.24/1.29  tff(f_63, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.24/1.29  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.24/1.29  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.24/1.29  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.24/1.29  tff(c_110, plain, (![A_47, B_48, C_49]: (k1_relset_1(A_47, B_48, C_49)=k1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.24/1.29  tff(c_119, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_110])).
% 2.24/1.29  tff(c_26, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.24/1.29  tff(c_120, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_26])).
% 2.24/1.29  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.29  tff(c_90, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.29  tff(c_93, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_90])).
% 2.24/1.29  tff(c_96, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_93])).
% 2.24/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.24/1.29  tff(c_125, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.24/1.29  tff(c_134, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_125])).
% 2.24/1.29  tff(c_146, plain, (![A_54, B_55, C_56]: (m1_subset_1(k2_relset_1(A_54, B_55, C_56), k1_zfmisc_1(B_55)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.24/1.29  tff(c_160, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_134, c_146])).
% 2.24/1.29  tff(c_165, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_160])).
% 2.24/1.29  tff(c_8, plain, (![A_2, B_3]: (m1_subset_1('#skF_1'(A_2, B_3), A_2) | k1_xboole_0=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.29  tff(c_98, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43, B_44), B_44) | k1_xboole_0=B_44 | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.29  tff(c_24, plain, (![D_32]: (~r2_hidden(D_32, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_32, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.24/1.29  tff(c_103, plain, (![A_43]: (~m1_subset_1('#skF_1'(A_43, k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_98, c_24])).
% 2.24/1.29  tff(c_187, plain, (![A_43]: (~m1_subset_1('#skF_1'(A_43, k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_134, c_134, c_103])).
% 2.24/1.29  tff(c_189, plain, (![A_60]: (~m1_subset_1('#skF_1'(A_60, k2_relat_1('#skF_4')), '#skF_3') | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_60)))), inference(splitLeft, [status(thm)], [c_187])).
% 2.24/1.29  tff(c_193, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_189])).
% 2.24/1.29  tff(c_196, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_165, c_193])).
% 2.24/1.29  tff(c_16, plain, (![A_11]: (~v1_xboole_0(k2_relat_1(A_11)) | ~v1_relat_1(A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.29  tff(c_204, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_196, c_16])).
% 2.24/1.29  tff(c_208, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2, c_204])).
% 2.24/1.29  tff(c_40, plain, (![A_36]: (v1_xboole_0(k1_relat_1(A_36)) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.29  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.24/1.29  tff(c_44, plain, (![A_36]: (k1_relat_1(A_36)=k1_xboole_0 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_40, c_4])).
% 2.24/1.29  tff(c_212, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_208, c_44])).
% 2.24/1.29  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_212])).
% 2.24/1.29  tff(c_220, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_187])).
% 2.24/1.29  tff(c_227, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_220, c_16])).
% 2.24/1.29  tff(c_231, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2, c_227])).
% 2.24/1.29  tff(c_235, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_231, c_44])).
% 2.24/1.29  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_235])).
% 2.24/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  Inference rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Ref     : 0
% 2.24/1.29  #Sup     : 44
% 2.24/1.29  #Fact    : 0
% 2.24/1.29  #Define  : 0
% 2.24/1.29  #Split   : 2
% 2.24/1.29  #Chain   : 0
% 2.24/1.29  #Close   : 0
% 2.24/1.29  
% 2.24/1.29  Ordering : KBO
% 2.24/1.29  
% 2.24/1.29  Simplification rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Subsume      : 1
% 2.24/1.29  #Demod        : 28
% 2.24/1.29  #Tautology    : 18
% 2.24/1.29  #SimpNegUnit  : 2
% 2.24/1.29  #BackRed      : 9
% 2.24/1.29  
% 2.24/1.29  #Partial instantiations: 0
% 2.24/1.29  #Strategies tried      : 1
% 2.24/1.29  
% 2.24/1.29  Timing (in seconds)
% 2.24/1.29  ----------------------
% 2.24/1.29  Preprocessing        : 0.32
% 2.24/1.29  Parsing              : 0.17
% 2.24/1.29  CNF conversion       : 0.02
% 2.24/1.29  Main loop            : 0.20
% 2.24/1.29  Inferencing          : 0.07
% 2.24/1.29  Reduction            : 0.06
% 2.24/1.29  Demodulation         : 0.04
% 2.24/1.29  BG Simplification    : 0.01
% 2.24/1.29  Subsumption          : 0.04
% 2.24/1.29  Abstraction          : 0.01
% 2.24/1.29  MUC search           : 0.00
% 2.24/1.29  Cooper               : 0.00
% 2.24/1.29  Total                : 0.55
% 2.24/1.29  Index Insertion      : 0.00
% 2.24/1.29  Index Deletion       : 0.00
% 2.24/1.29  Index Matching       : 0.00
% 2.24/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
