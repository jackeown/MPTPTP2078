%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:48 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 438 expanded)
%              Number of leaves         :   32 ( 158 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 (1117 expanded)
%              Number of equality atoms :   40 ( 251 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_99,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_200,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_218,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_200])).

tff(c_219,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_48,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_261,plain,(
    ! [D_72,C_73,B_74,A_75] :
      ( k1_funct_1(k2_funct_1(D_72),k1_funct_1(D_72,C_73)) = C_73
      | k1_xboole_0 = B_74
      | ~ r2_hidden(C_73,A_75)
      | ~ v2_funct_1(D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74)))
      | ~ v1_funct_2(D_72,A_75,B_74)
      | ~ v1_funct_1(D_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_268,plain,(
    ! [D_76,B_77] :
      ( k1_funct_1(k2_funct_1(D_76),k1_funct_1(D_76,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_77
      | ~ v2_funct_1(D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_77)))
      | ~ v1_funct_2(D_76,'#skF_1',B_77)
      | ~ v1_funct_1(D_76) ) ),
    inference(resolution,[status(thm)],[c_40,c_261])).

tff(c_273,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_268])).

tff(c_280,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_273])).

tff(c_282,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_301,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_2])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_301])).

tff(c_305,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_304,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_38,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_306,plain,(
    ! [D_78,B_79] :
      ( k1_funct_1(k2_funct_1(D_78),k1_funct_1(D_78,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_79
      | ~ v2_funct_1(D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_79)))
      | ~ v1_funct_2(D_78,'#skF_1',B_79)
      | ~ v1_funct_1(D_78) ) ),
    inference(resolution,[status(thm)],[c_42,c_261])).

tff(c_311,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_306])).

tff(c_318,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_38,c_311])).

tff(c_337,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_318])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_36,c_337])).

tff(c_340,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_81,plain,(
    ! [B_35,A_36] :
      ( ~ v1_xboole_0(B_35)
      | B_35 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_2,c_81])).

tff(c_353,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_340,c_84])).

tff(c_339,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_346,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_339,c_84])).

tff(c_396,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_346])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_180,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_185,plain,(
    ! [A_54,A_6] :
      ( m1_subset_1(A_54,A_6)
      | ~ r2_hidden(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_180])).

tff(c_377,plain,(
    ! [A_54,A_6] :
      ( m1_subset_1(A_54,A_6)
      | ~ r2_hidden(A_54,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_185])).

tff(c_575,plain,(
    ! [A_98,A_99] :
      ( m1_subset_1(A_98,A_99)
      | ~ r2_hidden(A_98,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_377])).

tff(c_643,plain,(
    ! [A_101] : m1_subset_1('#skF_3',A_101) ),
    inference(resolution,[status(thm)],[c_42,c_575])).

tff(c_32,plain,(
    ! [C_22,A_19,B_20] :
      ( v1_xboole_0(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_659,plain,(
    ! [A_19] :
      ( v1_xboole_0('#skF_3')
      | ~ v1_xboole_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_643,c_32])).

tff(c_704,plain,(
    ! [A_19] : ~ v1_xboole_0(A_19) ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_582,plain,(
    ! [A_100] : m1_subset_1('#skF_4',A_100) ),
    inference(resolution,[status(thm)],[c_40,c_575])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_207,plain,(
    ! [C_63] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_200])).

tff(c_217,plain,(
    ! [C_63] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_207])).

tff(c_557,plain,(
    ! [C_63] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_217])).

tff(c_602,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_582,c_557])).

tff(c_707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_602])).

tff(c_708,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_384,plain,(
    ! [A_36] :
      ( A_36 = '#skF_2'
      | ~ v1_xboole_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_84])).

tff(c_475,plain,(
    ! [A_36] :
      ( A_36 = '#skF_1'
      | ~ v1_xboole_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_384])).

tff(c_613,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_602,c_475])).

tff(c_731,plain,(
    ! [A_110] :
      ( A_110 = '#skF_4'
      | ~ v1_xboole_0(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_475])).

tff(c_734,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_708,c_731])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:05:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.46  
% 2.92/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.92/1.46  
% 2.92/1.46  %Foreground sorts:
% 2.92/1.46  
% 2.92/1.46  
% 2.92/1.46  %Background operators:
% 2.92/1.46  
% 2.92/1.46  
% 2.92/1.46  %Foreground operators:
% 2.92/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.92/1.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.92/1.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.92/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.92/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.92/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.92/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.92/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.92/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.46  
% 2.92/1.48  tff(f_117, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.92/1.48  tff(f_85, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.92/1.48  tff(f_99, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.92/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.92/1.48  tff(f_38, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.92/1.48  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.92/1.48  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.92/1.48  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.92/1.48  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.92/1.48  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.92/1.48  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.92/1.48  tff(c_200, plain, (![C_63, A_64, B_65]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.92/1.48  tff(c_218, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_200])).
% 2.92/1.48  tff(c_219, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_218])).
% 2.92/1.48  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.92/1.48  tff(c_48, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.92/1.48  tff(c_44, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.92/1.48  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.92/1.48  tff(c_261, plain, (![D_72, C_73, B_74, A_75]: (k1_funct_1(k2_funct_1(D_72), k1_funct_1(D_72, C_73))=C_73 | k1_xboole_0=B_74 | ~r2_hidden(C_73, A_75) | ~v2_funct_1(D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))) | ~v1_funct_2(D_72, A_75, B_74) | ~v1_funct_1(D_72))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.48  tff(c_268, plain, (![D_76, B_77]: (k1_funct_1(k2_funct_1(D_76), k1_funct_1(D_76, '#skF_4'))='#skF_4' | k1_xboole_0=B_77 | ~v2_funct_1(D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_77))) | ~v1_funct_2(D_76, '#skF_1', B_77) | ~v1_funct_1(D_76))), inference(resolution, [status(thm)], [c_40, c_261])).
% 2.92/1.48  tff(c_273, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_268])).
% 2.92/1.48  tff(c_280, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_273])).
% 2.92/1.48  tff(c_282, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_280])).
% 2.92/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.92/1.48  tff(c_301, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_2])).
% 2.92/1.48  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_301])).
% 2.92/1.48  tff(c_305, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_280])).
% 2.92/1.48  tff(c_304, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_280])).
% 2.92/1.48  tff(c_38, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.92/1.48  tff(c_306, plain, (![D_78, B_79]: (k1_funct_1(k2_funct_1(D_78), k1_funct_1(D_78, '#skF_3'))='#skF_3' | k1_xboole_0=B_79 | ~v2_funct_1(D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_79))) | ~v1_funct_2(D_78, '#skF_1', B_79) | ~v1_funct_1(D_78))), inference(resolution, [status(thm)], [c_42, c_261])).
% 2.92/1.48  tff(c_311, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_306])).
% 2.92/1.48  tff(c_318, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_38, c_311])).
% 2.92/1.48  tff(c_337, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_318])).
% 2.92/1.48  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_36, c_337])).
% 2.92/1.48  tff(c_340, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_218])).
% 2.92/1.48  tff(c_81, plain, (![B_35, A_36]: (~v1_xboole_0(B_35) | B_35=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.92/1.48  tff(c_84, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_2, c_81])).
% 2.92/1.48  tff(c_353, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_340, c_84])).
% 2.92/1.48  tff(c_339, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_218])).
% 2.92/1.48  tff(c_346, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_339, c_84])).
% 2.92/1.48  tff(c_396, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_346])).
% 2.92/1.48  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.92/1.48  tff(c_180, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.48  tff(c_185, plain, (![A_54, A_6]: (m1_subset_1(A_54, A_6) | ~r2_hidden(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_180])).
% 2.92/1.48  tff(c_377, plain, (![A_54, A_6]: (m1_subset_1(A_54, A_6) | ~r2_hidden(A_54, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_185])).
% 2.92/1.48  tff(c_575, plain, (![A_98, A_99]: (m1_subset_1(A_98, A_99) | ~r2_hidden(A_98, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_377])).
% 2.92/1.48  tff(c_643, plain, (![A_101]: (m1_subset_1('#skF_3', A_101))), inference(resolution, [status(thm)], [c_42, c_575])).
% 2.92/1.48  tff(c_32, plain, (![C_22, A_19, B_20]: (v1_xboole_0(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.92/1.48  tff(c_659, plain, (![A_19]: (v1_xboole_0('#skF_3') | ~v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_643, c_32])).
% 2.92/1.48  tff(c_704, plain, (![A_19]: (~v1_xboole_0(A_19))), inference(splitLeft, [status(thm)], [c_659])).
% 2.92/1.48  tff(c_582, plain, (![A_100]: (m1_subset_1('#skF_4', A_100))), inference(resolution, [status(thm)], [c_40, c_575])).
% 2.92/1.48  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.48  tff(c_207, plain, (![C_63]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_200])).
% 2.92/1.48  tff(c_217, plain, (![C_63]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_207])).
% 2.92/1.48  tff(c_557, plain, (![C_63]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_217])).
% 2.92/1.48  tff(c_602, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_582, c_557])).
% 2.92/1.48  tff(c_707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_602])).
% 2.92/1.48  tff(c_708, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_659])).
% 2.92/1.48  tff(c_384, plain, (![A_36]: (A_36='#skF_2' | ~v1_xboole_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_84])).
% 2.92/1.48  tff(c_475, plain, (![A_36]: (A_36='#skF_1' | ~v1_xboole_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_384])).
% 2.92/1.48  tff(c_613, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_602, c_475])).
% 2.92/1.48  tff(c_731, plain, (![A_110]: (A_110='#skF_4' | ~v1_xboole_0(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_475])).
% 2.92/1.48  tff(c_734, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_708, c_731])).
% 2.92/1.48  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_734])).
% 2.92/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.48  
% 2.92/1.48  Inference rules
% 2.92/1.48  ----------------------
% 2.92/1.48  #Ref     : 0
% 2.92/1.48  #Sup     : 143
% 2.92/1.48  #Fact    : 0
% 2.92/1.48  #Define  : 0
% 2.92/1.48  #Split   : 5
% 2.92/1.48  #Chain   : 0
% 2.92/1.48  #Close   : 0
% 2.92/1.48  
% 2.92/1.48  Ordering : KBO
% 2.92/1.48  
% 2.92/1.48  Simplification rules
% 2.92/1.48  ----------------------
% 2.92/1.48  #Subsume      : 10
% 2.92/1.48  #Demod        : 172
% 2.92/1.48  #Tautology    : 80
% 2.92/1.48  #SimpNegUnit  : 5
% 2.92/1.48  #BackRed      : 69
% 2.92/1.48  
% 2.92/1.48  #Partial instantiations: 0
% 2.92/1.48  #Strategies tried      : 1
% 2.92/1.48  
% 2.92/1.48  Timing (in seconds)
% 2.92/1.48  ----------------------
% 2.92/1.48  Preprocessing        : 0.31
% 2.92/1.48  Parsing              : 0.17
% 2.92/1.48  CNF conversion       : 0.02
% 2.92/1.48  Main loop            : 0.38
% 2.92/1.48  Inferencing          : 0.12
% 2.92/1.48  Reduction            : 0.13
% 2.92/1.48  Demodulation         : 0.09
% 2.92/1.48  BG Simplification    : 0.02
% 2.92/1.48  Subsumption          : 0.06
% 2.92/1.48  Abstraction          : 0.01
% 2.92/1.48  MUC search           : 0.00
% 2.92/1.48  Cooper               : 0.00
% 2.92/1.48  Total                : 0.73
% 2.92/1.48  Index Insertion      : 0.00
% 2.92/1.48  Index Deletion       : 0.00
% 2.92/1.48  Index Matching       : 0.00
% 2.92/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
