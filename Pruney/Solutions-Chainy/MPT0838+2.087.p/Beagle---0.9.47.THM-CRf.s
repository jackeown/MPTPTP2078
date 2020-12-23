%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:21 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 117 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 226 expanded)
%              Number of equality atoms :   26 (  63 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_22,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_31,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_31])).

tff(c_37,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34])).

tff(c_38,plain,(
    ! [A_38] :
      ( k2_relat_1(A_38) = k1_xboole_0
      | k1_relat_1(A_38) != k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_45,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_38])).

tff(c_53,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_54,plain,(
    ! [A_40] :
      ( k1_relat_1(A_40) = k1_xboole_0
      | k2_relat_1(A_40) != k1_xboole_0
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_54])).

tff(c_63,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_57])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_44,B_45,C_46] :
      ( k2_relset_1(A_44,B_45,C_46) = k2_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_69])).

tff(c_20,plain,(
    ! [D_32] :
      ( ~ r2_hidden(D_32,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_32,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_79,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k2_relat_1('#skF_4'))
      | ~ m1_subset_1(D_47,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_20])).

tff(c_83,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_86,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_83])).

tff(c_114,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k2_relset_1(A_56,B_57,C_58),k1_zfmisc_1(B_57))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_130,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_114])).

tff(c_136,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_130])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_59] :
      ( m1_subset_1(A_59,'#skF_3')
      | ~ r2_hidden(A_59,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_149,plain,
    ( m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_145])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_86,c_149])).

tff(c_155,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_213,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_216,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_213])).

tff(c_218,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_216])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:24:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.62  
% 2.50/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.63  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.50/1.63  
% 2.50/1.63  %Foreground sorts:
% 2.50/1.63  
% 2.50/1.63  
% 2.50/1.63  %Background operators:
% 2.50/1.63  
% 2.50/1.63  
% 2.50/1.63  %Foreground operators:
% 2.50/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.50/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.50/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.63  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.63  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.50/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.63  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.63  
% 2.50/1.65  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.50/1.65  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.50/1.65  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.50/1.65  tff(f_54, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.50/1.65  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.50/1.65  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.50/1.65  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.50/1.65  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.50/1.65  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.50/1.65  tff(c_22, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.50/1.65  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.50/1.65  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.50/1.65  tff(c_31, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.50/1.65  tff(c_34, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_31])).
% 2.50/1.65  tff(c_37, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34])).
% 2.50/1.65  tff(c_38, plain, (![A_38]: (k2_relat_1(A_38)=k1_xboole_0 | k1_relat_1(A_38)!=k1_xboole_0 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.65  tff(c_45, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_38])).
% 2.50/1.65  tff(c_53, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_45])).
% 2.50/1.65  tff(c_54, plain, (![A_40]: (k1_relat_1(A_40)=k1_xboole_0 | k2_relat_1(A_40)!=k1_xboole_0 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.65  tff(c_57, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_54])).
% 2.50/1.65  tff(c_63, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_53, c_57])).
% 2.50/1.65  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.65  tff(c_69, plain, (![A_44, B_45, C_46]: (k2_relset_1(A_44, B_45, C_46)=k2_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.65  tff(c_73, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_69])).
% 2.50/1.65  tff(c_20, plain, (![D_32]: (~r2_hidden(D_32, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_32, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.50/1.65  tff(c_79, plain, (![D_47]: (~r2_hidden(D_47, k2_relat_1('#skF_4')) | ~m1_subset_1(D_47, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_20])).
% 2.50/1.65  tff(c_83, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_79])).
% 2.50/1.65  tff(c_86, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_83])).
% 2.50/1.65  tff(c_114, plain, (![A_56, B_57, C_58]: (m1_subset_1(k2_relset_1(A_56, B_57, C_58), k1_zfmisc_1(B_57)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.50/1.65  tff(c_130, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_73, c_114])).
% 2.50/1.65  tff(c_136, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_130])).
% 2.50/1.65  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.65  tff(c_145, plain, (![A_59]: (m1_subset_1(A_59, '#skF_3') | ~r2_hidden(A_59, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_136, c_4])).
% 2.50/1.65  tff(c_149, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_145])).
% 2.50/1.65  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_86, c_149])).
% 2.50/1.65  tff(c_155, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_45])).
% 2.50/1.65  tff(c_213, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.50/1.65  tff(c_216, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_213])).
% 2.50/1.65  tff(c_218, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_155, c_216])).
% 2.50/1.65  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_218])).
% 2.50/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.65  
% 2.50/1.65  Inference rules
% 2.50/1.65  ----------------------
% 2.50/1.65  #Ref     : 0
% 2.50/1.65  #Sup     : 40
% 2.50/1.65  #Fact    : 0
% 2.50/1.65  #Define  : 0
% 2.50/1.65  #Split   : 2
% 2.50/1.65  #Chain   : 0
% 2.50/1.65  #Close   : 0
% 2.50/1.65  
% 2.50/1.65  Ordering : KBO
% 2.50/1.65  
% 2.50/1.65  Simplification rules
% 2.50/1.65  ----------------------
% 2.50/1.65  #Subsume      : 2
% 2.50/1.65  #Demod        : 13
% 2.50/1.65  #Tautology    : 19
% 2.50/1.65  #SimpNegUnit  : 5
% 2.50/1.65  #BackRed      : 3
% 2.50/1.65  
% 2.50/1.65  #Partial instantiations: 0
% 2.50/1.65  #Strategies tried      : 1
% 2.50/1.65  
% 2.50/1.65  Timing (in seconds)
% 2.50/1.65  ----------------------
% 2.50/1.65  Preprocessing        : 0.50
% 2.50/1.65  Parsing              : 0.26
% 2.50/1.65  CNF conversion       : 0.04
% 2.50/1.65  Main loop            : 0.30
% 2.50/1.66  Inferencing          : 0.12
% 2.50/1.66  Reduction            : 0.09
% 2.50/1.66  Demodulation         : 0.06
% 2.50/1.66  BG Simplification    : 0.02
% 2.50/1.66  Subsumption          : 0.04
% 2.50/1.66  Abstraction          : 0.02
% 2.50/1.66  MUC search           : 0.00
% 2.50/1.66  Cooper               : 0.00
% 2.50/1.66  Total                : 0.85
% 2.50/1.66  Index Insertion      : 0.00
% 2.50/1.66  Index Deletion       : 0.00
% 2.50/1.66  Index Matching       : 0.00
% 2.50/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
