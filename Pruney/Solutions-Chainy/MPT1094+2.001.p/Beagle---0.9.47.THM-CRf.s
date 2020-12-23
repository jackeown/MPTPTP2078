%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:26 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   96 ( 140 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k9_funct_3 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k9_funct_3,type,(
    k9_funct_3: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_finset_1(k1_relat_1(A))
        <=> v1_finset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_finset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_funct_1(k9_funct_3(A,B))
      & v1_funct_2(k9_funct_3(A,B),k2_zfmisc_1(A,B),A)
      & m1_subset_1(k9_funct_3(A,B),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_funct_3)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k9_relat_1(k9_funct_3(k1_relat_1(A),k2_relat_1(A)),A) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_funct_3)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_finset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_finset_1(k1_relat_1(A))
       => v1_finset_1(k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_finset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_finset_1(B)
     => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_finset_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_37,plain,(
    ~ v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( v1_finset_1(k1_relat_1('#skF_1'))
    | v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    v1_finset_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_34])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,(
    ! [A_30,B_31] : m1_subset_1(k9_funct_3(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_30,B_31),A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_30,B_31] :
      ( v1_relat_1(k9_funct_3(A_30,B_31))
      | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_30,B_31),A_30)) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_61,plain,(
    ! [A_30,B_31] : v1_relat_1(k9_funct_3(A_30,B_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_8,plain,(
    ! [A_7,B_8] : v1_funct_1(k9_funct_3(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,(
    ! [A_40] :
      ( k9_relat_1(k9_funct_3(k1_relat_1(A_40),k2_relat_1(A_40)),A_40) = k1_relat_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_finset_1(k9_relat_1(A_11,B_12))
      | ~ v1_finset_1(B_12)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [A_40] :
      ( v1_finset_1(k1_relat_1(A_40))
      | ~ v1_finset_1(A_40)
      | ~ v1_funct_1(k9_funct_3(k1_relat_1(A_40),k2_relat_1(A_40)))
      | ~ v1_relat_1(k9_funct_3(k1_relat_1(A_40),k2_relat_1(A_40)))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_16])).

tff(c_90,plain,(
    ! [A_41] :
      ( v1_finset_1(k1_relat_1(A_41))
      | ~ v1_finset_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_8,c_82])).

tff(c_96,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_37])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_38,c_96])).

tff(c_102,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_103,plain,(
    v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_22,plain,(
    ! [A_16] :
      ( v1_finset_1(k2_relat_1(A_16))
      | ~ v1_finset_1(k1_relat_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( v1_finset_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_finset_1(B_14)
      | ~ v1_finset_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_120,plain,(
    ! [A_57] :
      ( k3_xboole_0(A_57,k2_zfmisc_1(k1_relat_1(A_57),k2_relat_1(A_57))) = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( v1_finset_1(k3_xboole_0(A_9,B_10))
      | ~ v1_finset_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_132,plain,(
    ! [A_58] :
      ( v1_finset_1(A_58)
      | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(A_58),k2_relat_1(A_58)))
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_14])).

tff(c_137,plain,(
    ! [A_59] :
      ( v1_finset_1(A_59)
      | ~ v1_relat_1(A_59)
      | ~ v1_finset_1(k2_relat_1(A_59))
      | ~ v1_finset_1(k1_relat_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_18,c_132])).

tff(c_157,plain,(
    ! [A_62] :
      ( v1_finset_1(A_62)
      | ~ v1_finset_1(k1_relat_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_22,c_137])).

tff(c_163,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_103,c_157])).

tff(c_167,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_163])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.19  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k9_funct_3 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1
% 1.96/1.19  
% 1.96/1.19  %Foreground sorts:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Background operators:
% 1.96/1.19  
% 1.96/1.19  
% 1.96/1.19  %Foreground operators:
% 1.96/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.19  tff(k9_funct_3, type, k9_funct_3: ($i * $i) > $i).
% 1.96/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.96/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.19  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.96/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.19  
% 2.07/1.20  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_finset_1(k1_relat_1(A)) <=> v1_finset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_finset_1)).
% 2.07/1.20  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.07/1.20  tff(f_44, axiom, (![A, B]: ((v1_funct_1(k9_funct_3(A, B)) & v1_funct_2(k9_funct_3(A, B), k2_zfmisc_1(A, B), A)) & m1_subset_1(k9_funct_3(A, B), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_funct_3)).
% 2.07/1.20  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.07/1.20  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (k9_relat_1(k9_funct_3(k1_relat_1(A), k2_relat_1(A)), A) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_funct_3)).
% 2.07/1.20  tff(f_56, axiom, (![A, B]: (((v1_relat_1(A) & v1_funct_1(A)) & v1_finset_1(B)) => v1_finset_1(k9_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_finset_1)).
% 2.07/1.20  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_finset_1(k1_relat_1(A)) => v1_finset_1(k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_finset_1)).
% 2.07/1.20  tff(f_62, axiom, (![A, B]: ((v1_finset_1(A) & v1_finset_1(B)) => v1_finset_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_finset_1)).
% 2.07/1.20  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 2.07/1.20  tff(f_48, axiom, (![A, B]: (v1_finset_1(B) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_finset_1)).
% 2.07/1.20  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.07/1.20  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.07/1.20  tff(c_28, plain, (~v1_finset_1('#skF_1') | ~v1_finset_1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.07/1.20  tff(c_37, plain, (~v1_finset_1(k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.07/1.20  tff(c_34, plain, (v1_finset_1(k1_relat_1('#skF_1')) | v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.07/1.20  tff(c_38, plain, (v1_finset_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_37, c_34])).
% 2.07/1.20  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.07/1.20  tff(c_55, plain, (![A_30, B_31]: (m1_subset_1(k9_funct_3(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_30, B_31), A_30))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.20  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.20  tff(c_58, plain, (![A_30, B_31]: (v1_relat_1(k9_funct_3(A_30, B_31)) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_30, B_31), A_30)))), inference(resolution, [status(thm)], [c_55, c_2])).
% 2.07/1.20  tff(c_61, plain, (![A_30, B_31]: (v1_relat_1(k9_funct_3(A_30, B_31)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_58])).
% 2.07/1.20  tff(c_8, plain, (![A_7, B_8]: (v1_funct_1(k9_funct_3(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.20  tff(c_76, plain, (![A_40]: (k9_relat_1(k9_funct_3(k1_relat_1(A_40), k2_relat_1(A_40)), A_40)=k1_relat_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.20  tff(c_16, plain, (![A_11, B_12]: (v1_finset_1(k9_relat_1(A_11, B_12)) | ~v1_finset_1(B_12) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.20  tff(c_82, plain, (![A_40]: (v1_finset_1(k1_relat_1(A_40)) | ~v1_finset_1(A_40) | ~v1_funct_1(k9_funct_3(k1_relat_1(A_40), k2_relat_1(A_40))) | ~v1_relat_1(k9_funct_3(k1_relat_1(A_40), k2_relat_1(A_40))) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_76, c_16])).
% 2.07/1.20  tff(c_90, plain, (![A_41]: (v1_finset_1(k1_relat_1(A_41)) | ~v1_finset_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_8, c_82])).
% 2.07/1.20  tff(c_96, plain, (~v1_finset_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_90, c_37])).
% 2.07/1.20  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_38, c_96])).
% 2.07/1.20  tff(c_102, plain, (~v1_finset_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.07/1.20  tff(c_103, plain, (v1_finset_1(k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_28])).
% 2.07/1.20  tff(c_22, plain, (![A_16]: (v1_finset_1(k2_relat_1(A_16)) | ~v1_finset_1(k1_relat_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.07/1.20  tff(c_18, plain, (![A_13, B_14]: (v1_finset_1(k2_zfmisc_1(A_13, B_14)) | ~v1_finset_1(B_14) | ~v1_finset_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.20  tff(c_120, plain, (![A_57]: (k3_xboole_0(A_57, k2_zfmisc_1(k1_relat_1(A_57), k2_relat_1(A_57)))=A_57 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.07/1.20  tff(c_14, plain, (![A_9, B_10]: (v1_finset_1(k3_xboole_0(A_9, B_10)) | ~v1_finset_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.20  tff(c_132, plain, (![A_58]: (v1_finset_1(A_58) | ~v1_finset_1(k2_zfmisc_1(k1_relat_1(A_58), k2_relat_1(A_58))) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_120, c_14])).
% 2.07/1.20  tff(c_137, plain, (![A_59]: (v1_finset_1(A_59) | ~v1_relat_1(A_59) | ~v1_finset_1(k2_relat_1(A_59)) | ~v1_finset_1(k1_relat_1(A_59)))), inference(resolution, [status(thm)], [c_18, c_132])).
% 2.07/1.20  tff(c_157, plain, (![A_62]: (v1_finset_1(A_62) | ~v1_finset_1(k1_relat_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_22, c_137])).
% 2.07/1.20  tff(c_163, plain, (v1_finset_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_103, c_157])).
% 2.07/1.20  tff(c_167, plain, (v1_finset_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_163])).
% 2.07/1.20  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_167])).
% 2.07/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.20  
% 2.07/1.20  Inference rules
% 2.07/1.20  ----------------------
% 2.07/1.20  #Ref     : 0
% 2.07/1.20  #Sup     : 22
% 2.07/1.20  #Fact    : 0
% 2.07/1.20  #Define  : 0
% 2.07/1.20  #Split   : 1
% 2.07/1.20  #Chain   : 0
% 2.07/1.20  #Close   : 0
% 2.07/1.20  
% 2.07/1.20  Ordering : KBO
% 2.07/1.20  
% 2.07/1.20  Simplification rules
% 2.07/1.20  ----------------------
% 2.07/1.20  #Subsume      : 0
% 2.07/1.20  #Demod        : 12
% 2.07/1.20  #Tautology    : 13
% 2.07/1.20  #SimpNegUnit  : 3
% 2.07/1.20  #BackRed      : 0
% 2.07/1.20  
% 2.07/1.20  #Partial instantiations: 0
% 2.07/1.20  #Strategies tried      : 1
% 2.07/1.20  
% 2.07/1.20  Timing (in seconds)
% 2.07/1.20  ----------------------
% 2.07/1.21  Preprocessing        : 0.28
% 2.07/1.21  Parsing              : 0.16
% 2.07/1.21  CNF conversion       : 0.02
% 2.07/1.21  Main loop            : 0.17
% 2.07/1.21  Inferencing          : 0.08
% 2.07/1.21  Reduction            : 0.04
% 2.07/1.21  Demodulation         : 0.03
% 2.07/1.21  BG Simplification    : 0.01
% 2.07/1.21  Subsumption          : 0.02
% 2.07/1.21  Abstraction          : 0.01
% 2.07/1.21  MUC search           : 0.00
% 2.07/1.21  Cooper               : 0.00
% 2.07/1.21  Total                : 0.47
% 2.07/1.21  Index Insertion      : 0.00
% 2.07/1.21  Index Deletion       : 0.00
% 2.07/1.21  Index Matching       : 0.00
% 2.07/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
