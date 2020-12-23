%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:51 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 132 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  124 ( 457 expanded)
%              Number of equality atoms :   12 (  63 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_245,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_relset_1(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_251,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_245])).

tff(c_55,plain,(
    ! [A_28,B_29,D_30] :
      ( r2_relset_1(A_28,B_29,D_30,D_30)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_xboole_0(k2_zfmisc_1(A_3,B_4))
      | ~ v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_41,plain,(
    ! [B_26,A_27] :
      ( v1_xboole_0(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_50,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_134,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_partfun1(C_49,A_50)
      | ~ v1_funct_2(C_49,A_50,B_51)
      | ~ v1_funct_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | v1_xboole_0(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_143,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_149,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_143])).

tff(c_150,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_149])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_146,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_134])).

tff(c_153,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_146])).

tff(c_154,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_153])).

tff(c_22,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_197,plain,(
    ! [D_62,C_63,A_64,B_65] :
      ( D_62 = C_63
      | ~ r1_partfun1(C_63,D_62)
      | ~ v1_partfun1(D_62,A_64)
      | ~ v1_partfun1(C_63,A_64)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1(D_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_199,plain,(
    ! [A_64,B_65] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_64)
      | ~ v1_partfun1('#skF_3',A_64)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_197])).

tff(c_202,plain,(
    ! [A_64,B_65] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_64)
      | ~ v1_partfun1('#skF_3',A_64)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_199])).

tff(c_204,plain,(
    ! [A_66,B_67] :
      ( ~ v1_partfun1('#skF_4',A_66)
      | ~ v1_partfun1('#skF_3',A_66)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_207,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_30,c_204])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_150,c_154,c_207])).

tff(c_212,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_216,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_18])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_216])).

tff(c_226,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_227,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_49,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_228,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_228])).

tff(c_237,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_256,plain,(
    ! [A_71] :
      ( A_71 = '#skF_4'
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_237,c_2])).

tff(c_272,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_226,c_256])).

tff(c_277,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_18])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.39  
% 2.35/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.39  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.39  
% 2.35/1.39  %Foreground sorts:
% 2.35/1.39  
% 2.35/1.39  
% 2.35/1.39  %Background operators:
% 2.35/1.39  
% 2.35/1.39  
% 2.35/1.39  %Foreground operators:
% 2.35/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.39  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.35/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.39  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.35/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.39  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.35/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.39  
% 2.60/1.41  tff(f_106, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.60/1.41  tff(f_52, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.60/1.41  tff(f_37, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.60/1.41  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.60/1.41  tff(f_66, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.60/1.41  tff(f_83, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.60/1.41  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.60/1.41  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.60/1.41  tff(c_245, plain, (![A_68, B_69, D_70]: (r2_relset_1(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.41  tff(c_251, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_245])).
% 2.60/1.41  tff(c_55, plain, (![A_28, B_29, D_30]: (r2_relset_1(A_28, B_29, D_30, D_30) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.41  tff(c_61, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_55])).
% 2.60/1.41  tff(c_4, plain, (![A_3, B_4]: (v1_xboole_0(k2_zfmisc_1(A_3, B_4)) | ~v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.60/1.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.60/1.41  tff(c_41, plain, (![B_26, A_27]: (v1_xboole_0(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.60/1.41  tff(c_48, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_41])).
% 2.60/1.41  tff(c_50, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.60/1.41  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4, c_50])).
% 2.60/1.41  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.60/1.41  tff(c_32, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.60/1.41  tff(c_134, plain, (![C_49, A_50, B_51]: (v1_partfun1(C_49, A_50) | ~v1_funct_2(C_49, A_50, B_51) | ~v1_funct_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | v1_xboole_0(B_51))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.41  tff(c_143, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_134])).
% 2.60/1.41  tff(c_149, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_143])).
% 2.60/1.41  tff(c_150, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_149])).
% 2.60/1.41  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.60/1.41  tff(c_26, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.60/1.41  tff(c_146, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_134])).
% 2.60/1.41  tff(c_153, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_146])).
% 2.60/1.41  tff(c_154, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_153])).
% 2.60/1.41  tff(c_22, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.60/1.41  tff(c_197, plain, (![D_62, C_63, A_64, B_65]: (D_62=C_63 | ~r1_partfun1(C_63, D_62) | ~v1_partfun1(D_62, A_64) | ~v1_partfun1(C_63, A_64) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1(D_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.60/1.41  tff(c_199, plain, (![A_64, B_65]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_64) | ~v1_partfun1('#skF_3', A_64) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_197])).
% 2.60/1.41  tff(c_202, plain, (![A_64, B_65]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_64) | ~v1_partfun1('#skF_3', A_64) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_199])).
% 2.60/1.41  tff(c_204, plain, (![A_66, B_67]: (~v1_partfun1('#skF_4', A_66) | ~v1_partfun1('#skF_3', A_66) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(splitLeft, [status(thm)], [c_202])).
% 2.60/1.41  tff(c_207, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_30, c_204])).
% 2.60/1.41  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_150, c_154, c_207])).
% 2.60/1.41  tff(c_212, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_202])).
% 2.60/1.41  tff(c_18, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.60/1.41  tff(c_216, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_18])).
% 2.60/1.41  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_216])).
% 2.60/1.41  tff(c_226, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.60/1.41  tff(c_227, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 2.60/1.41  tff(c_49, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.60/1.41  tff(c_228, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_49])).
% 2.60/1.41  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_228])).
% 2.60/1.41  tff(c_237, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_49])).
% 2.60/1.41  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.41  tff(c_256, plain, (![A_71]: (A_71='#skF_4' | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_237, c_2])).
% 2.60/1.41  tff(c_272, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_226, c_256])).
% 2.60/1.41  tff(c_277, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_18])).
% 2.60/1.41  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_277])).
% 2.60/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.41  
% 2.60/1.41  Inference rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Ref     : 0
% 2.60/1.41  #Sup     : 61
% 2.60/1.41  #Fact    : 0
% 2.60/1.41  #Define  : 0
% 2.60/1.41  #Split   : 5
% 2.60/1.41  #Chain   : 0
% 2.60/1.41  #Close   : 0
% 2.60/1.41  
% 2.60/1.41  Ordering : KBO
% 2.60/1.41  
% 2.60/1.41  Simplification rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Subsume      : 27
% 2.60/1.41  #Demod        : 52
% 2.60/1.41  #Tautology    : 22
% 2.60/1.41  #SimpNegUnit  : 6
% 2.60/1.41  #BackRed      : 17
% 2.60/1.41  
% 2.60/1.41  #Partial instantiations: 0
% 2.60/1.41  #Strategies tried      : 1
% 2.60/1.41  
% 2.60/1.41  Timing (in seconds)
% 2.60/1.41  ----------------------
% 2.60/1.41  Preprocessing        : 0.31
% 2.60/1.41  Parsing              : 0.16
% 2.60/1.41  CNF conversion       : 0.02
% 2.60/1.41  Main loop            : 0.32
% 2.60/1.41  Inferencing          : 0.11
% 2.60/1.41  Reduction            : 0.08
% 2.60/1.41  Demodulation         : 0.06
% 2.60/1.41  BG Simplification    : 0.02
% 2.60/1.41  Subsumption          : 0.09
% 2.60/1.41  Abstraction          : 0.01
% 2.60/1.41  MUC search           : 0.00
% 2.60/1.41  Cooper               : 0.00
% 2.60/1.41  Total                : 0.66
% 2.60/1.41  Index Insertion      : 0.00
% 2.60/1.42  Index Deletion       : 0.00
% 2.60/1.42  Index Matching       : 0.00
% 2.60/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
