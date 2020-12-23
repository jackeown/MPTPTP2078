%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:13 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 215 expanded)
%              Number of equality atoms :   21 (  50 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_91,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_105,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_114,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_24,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_115,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_24])).

tff(c_88,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_121,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_130,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_121])).

tff(c_142,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k2_relset_1(A_51,B_52,C_53),k1_zfmisc_1(B_52))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_157,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_142])).

tff(c_162,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_157])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1('#skF_1'(A_2,B_3),A_2)
      | k1_xboole_0 = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),B_3)
      | k1_xboole_0 = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [D_30] :
      ( ~ r2_hidden(D_30,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_136,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_relat_1('#skF_4'))
      | ~ m1_subset_1(D_50,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_22])).

tff(c_141,plain,(
    ! [A_2] :
      ( ~ m1_subset_1('#skF_1'(A_2,k2_relat_1('#skF_4')),'#skF_3')
      | k2_relat_1('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_2)) ) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_175,plain,(
    ! [A_58] :
      ( ~ m1_subset_1('#skF_1'(A_58,k2_relat_1('#skF_4')),'#skF_3')
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_58)) ) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_179,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_175])).

tff(c_182,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_179])).

tff(c_12,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_190,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_12])).

tff(c_194,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2,c_190])).

tff(c_37,plain,(
    ! [A_32] :
      ( v1_xboole_0(k1_relat_1(A_32))
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_41,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) = k1_xboole_0
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_37,c_4])).

tff(c_207,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_41])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_207])).

tff(c_215,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_222,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_12])).

tff(c_226,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2,c_222])).

tff(c_230,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_226,c_41])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.33  
% 2.24/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.33  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.24/1.33  
% 2.24/1.33  %Foreground sorts:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Background operators:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Foreground operators:
% 2.24/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.33  
% 2.24/1.34  tff(f_91, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.24/1.34  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.24/1.34  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.24/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.24/1.34  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.24/1.34  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.24/1.34  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.24/1.34  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.24/1.34  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.24/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.24/1.34  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.34  tff(c_105, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.34  tff(c_114, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_105])).
% 2.24/1.34  tff(c_24, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.34  tff(c_115, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_24])).
% 2.24/1.34  tff(c_88, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.34  tff(c_92, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_88])).
% 2.24/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.24/1.34  tff(c_121, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.24/1.34  tff(c_130, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_121])).
% 2.24/1.34  tff(c_142, plain, (![A_51, B_52, C_53]: (m1_subset_1(k2_relset_1(A_51, B_52, C_53), k1_zfmisc_1(B_52)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.24/1.34  tff(c_157, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_130, c_142])).
% 2.24/1.34  tff(c_162, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_157])).
% 2.24/1.34  tff(c_8, plain, (![A_2, B_3]: (m1_subset_1('#skF_1'(A_2, B_3), A_2) | k1_xboole_0=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.34  tff(c_6, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), B_3) | k1_xboole_0=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.34  tff(c_22, plain, (![D_30]: (~r2_hidden(D_30, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.24/1.34  tff(c_136, plain, (![D_50]: (~r2_hidden(D_50, k2_relat_1('#skF_4')) | ~m1_subset_1(D_50, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_22])).
% 2.24/1.34  tff(c_141, plain, (![A_2]: (~m1_subset_1('#skF_1'(A_2, k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_2)))), inference(resolution, [status(thm)], [c_6, c_136])).
% 2.24/1.34  tff(c_175, plain, (![A_58]: (~m1_subset_1('#skF_1'(A_58, k2_relat_1('#skF_4')), '#skF_3') | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_58)))), inference(splitLeft, [status(thm)], [c_141])).
% 2.24/1.34  tff(c_179, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_175])).
% 2.24/1.34  tff(c_182, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_162, c_179])).
% 2.24/1.34  tff(c_12, plain, (![A_6]: (~v1_xboole_0(k2_relat_1(A_6)) | ~v1_relat_1(A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.24/1.34  tff(c_190, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_182, c_12])).
% 2.24/1.34  tff(c_194, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2, c_190])).
% 2.24/1.34  tff(c_37, plain, (![A_32]: (v1_xboole_0(k1_relat_1(A_32)) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.24/1.34  tff(c_41, plain, (![A_32]: (k1_relat_1(A_32)=k1_xboole_0 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_37, c_4])).
% 2.24/1.34  tff(c_207, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_194, c_41])).
% 2.24/1.34  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_207])).
% 2.24/1.34  tff(c_215, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_141])).
% 2.24/1.34  tff(c_222, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_215, c_12])).
% 2.24/1.34  tff(c_226, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2, c_222])).
% 2.24/1.34  tff(c_230, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_226, c_41])).
% 2.24/1.34  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_230])).
% 2.24/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.34  
% 2.24/1.34  Inference rules
% 2.24/1.34  ----------------------
% 2.24/1.34  #Ref     : 0
% 2.24/1.34  #Sup     : 45
% 2.24/1.34  #Fact    : 0
% 2.24/1.34  #Define  : 0
% 2.24/1.34  #Split   : 2
% 2.24/1.34  #Chain   : 0
% 2.24/1.34  #Close   : 0
% 2.24/1.34  
% 2.24/1.34  Ordering : KBO
% 2.24/1.34  
% 2.24/1.34  Simplification rules
% 2.24/1.34  ----------------------
% 2.24/1.34  #Subsume      : 0
% 2.24/1.34  #Demod        : 24
% 2.24/1.34  #Tautology    : 20
% 2.24/1.34  #SimpNegUnit  : 2
% 2.24/1.34  #BackRed      : 9
% 2.24/1.34  
% 2.24/1.34  #Partial instantiations: 0
% 2.24/1.34  #Strategies tried      : 1
% 2.24/1.34  
% 2.24/1.34  Timing (in seconds)
% 2.24/1.34  ----------------------
% 2.24/1.35  Preprocessing        : 0.32
% 2.24/1.35  Parsing              : 0.17
% 2.24/1.35  CNF conversion       : 0.02
% 2.24/1.35  Main loop            : 0.18
% 2.24/1.35  Inferencing          : 0.07
% 2.24/1.35  Reduction            : 0.05
% 2.24/1.35  Demodulation         : 0.04
% 2.24/1.35  BG Simplification    : 0.01
% 2.24/1.35  Subsumption          : 0.03
% 2.24/1.35  Abstraction          : 0.01
% 2.24/1.35  MUC search           : 0.00
% 2.24/1.35  Cooper               : 0.00
% 2.24/1.35  Total                : 0.53
% 2.24/1.35  Index Insertion      : 0.00
% 2.24/1.35  Index Deletion       : 0.00
% 2.24/1.35  Index Matching       : 0.00
% 2.24/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
