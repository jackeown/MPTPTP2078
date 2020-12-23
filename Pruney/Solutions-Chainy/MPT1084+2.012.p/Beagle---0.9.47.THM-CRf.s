%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:21 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 486 expanded)
%              Number of leaves         :   30 ( 197 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 (1496 expanded)
%              Number of equality atoms :   40 ( 337 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_74,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_143,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_funct_2(A_54,B_55,D_56,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(D_56,A_54,B_55)
      | ~ v1_funct_1(D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_148,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_152,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_148])).

tff(c_74,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_92,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_92])).

tff(c_112,plain,(
    ! [A_52,B_53] :
      ( k1_relset_1(A_52,A_52,B_53) = A_52
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_zfmisc_1(A_52,A_52)))
      | ~ v1_funct_2(B_53,A_52,A_52)
      | ~ v1_funct_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_119,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_123,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_101,c_119])).

tff(c_24,plain,(
    ! [A_18] : k6_relat_1(A_18) = k6_partfun1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_partfun1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_128,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_45])).

tff(c_135,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_40,c_123,c_123,c_128])).

tff(c_153,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_32,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_154,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_32])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_154])).

tff(c_159,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_10,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_170,plain,(
    ! [B_57] :
      ( k1_funct_1(B_57,'#skF_1'(k1_relat_1(B_57),B_57)) != '#skF_1'(k1_relat_1(B_57),B_57)
      | k6_partfun1(k1_relat_1(B_57)) = B_57
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_173,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_170])).

tff(c_175,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_40,c_123,c_123,c_173])).

tff(c_176,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_175])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_131,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),'#skF_3'),'#skF_2')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_45])).

tff(c_137,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_40,c_123,c_123,c_131])).

tff(c_160,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_160])).

tff(c_162,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_166,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_169,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_166])).

tff(c_34,plain,(
    ! [C_29] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_29) = C_29
      | ~ m1_subset_1(C_29,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_184,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_34])).

tff(c_207,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k3_funct_2(A_59,B_60,C_61,D_62) = k1_funct_1(C_61,D_62)
      | ~ m1_subset_1(D_62,A_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_2(C_61,A_59,B_60)
      | ~ v1_funct_1(C_61)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_211,plain,(
    ! [B_60,C_61] :
      ( k3_funct_2('#skF_2',B_60,C_61,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_61,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_60)))
      | ~ v1_funct_2(C_61,'#skF_2',B_60)
      | ~ v1_funct_1(C_61)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_169,c_207])).

tff(c_224,plain,(
    ! [B_63,C_64] :
      ( k3_funct_2('#skF_2',B_63,C_64,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_64,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_63)))
      | ~ v1_funct_2(C_64,'#skF_2',B_63)
      | ~ v1_funct_1(C_64) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_211])).

tff(c_231,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_224])).

tff(c_235,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_184,c_231])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.26  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.26  
% 2.18/1.26  %Foreground sorts:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Background operators:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Foreground operators:
% 2.18/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.26  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.18/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.26  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.18/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.26  
% 2.18/1.28  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.18/1.28  tff(f_90, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.18/1.28  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.18/1.28  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.18/1.28  tff(f_98, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.18/1.28  tff(f_74, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.18/1.28  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.18/1.28  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.18/1.28  tff(f_72, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.18/1.28  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.18/1.28  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.18/1.28  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.18/1.28  tff(c_143, plain, (![A_54, B_55, D_56]: (r2_funct_2(A_54, B_55, D_56, D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(D_56, A_54, B_55) | ~v1_funct_1(D_56))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.28  tff(c_148, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_143])).
% 2.18/1.28  tff(c_152, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_148])).
% 2.18/1.28  tff(c_74, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.28  tff(c_83, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_74])).
% 2.18/1.28  tff(c_92, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.28  tff(c_101, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_92])).
% 2.18/1.28  tff(c_112, plain, (![A_52, B_53]: (k1_relset_1(A_52, A_52, B_53)=A_52 | ~m1_subset_1(B_53, k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))) | ~v1_funct_2(B_53, A_52, A_52) | ~v1_funct_1(B_53))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.18/1.28  tff(c_119, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_112])).
% 2.18/1.28  tff(c_123, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_101, c_119])).
% 2.18/1.28  tff(c_24, plain, (![A_18]: (k6_relat_1(A_18)=k6_partfun1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.28  tff(c_12, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.28  tff(c_45, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_partfun1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 2.18/1.28  tff(c_128, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_45])).
% 2.18/1.28  tff(c_135, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_40, c_123, c_123, c_128])).
% 2.18/1.28  tff(c_153, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_135])).
% 2.18/1.28  tff(c_32, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.18/1.28  tff(c_154, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_32])).
% 2.18/1.28  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_154])).
% 2.18/1.28  tff(c_159, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_135])).
% 2.18/1.28  tff(c_10, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.28  tff(c_170, plain, (![B_57]: (k1_funct_1(B_57, '#skF_1'(k1_relat_1(B_57), B_57))!='#skF_1'(k1_relat_1(B_57), B_57) | k6_partfun1(k1_relat_1(B_57))=B_57 | ~v1_funct_1(B_57) | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10])).
% 2.18/1.28  tff(c_173, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_170])).
% 2.18/1.28  tff(c_175, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_40, c_123, c_123, c_173])).
% 2.18/1.28  tff(c_176, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_159, c_175])).
% 2.18/1.28  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.18/1.28  tff(c_131, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), '#skF_3'), '#skF_2') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_45])).
% 2.18/1.28  tff(c_137, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_40, c_123, c_123, c_131])).
% 2.18/1.28  tff(c_160, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_137])).
% 2.18/1.28  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_160])).
% 2.18/1.28  tff(c_162, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_137])).
% 2.18/1.28  tff(c_2, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~r2_hidden(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.28  tff(c_166, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_162, c_2])).
% 2.18/1.28  tff(c_169, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_166])).
% 2.18/1.28  tff(c_34, plain, (![C_29]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_29)=C_29 | ~m1_subset_1(C_29, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.18/1.28  tff(c_184, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_169, c_34])).
% 2.18/1.28  tff(c_207, plain, (![A_59, B_60, C_61, D_62]: (k3_funct_2(A_59, B_60, C_61, D_62)=k1_funct_1(C_61, D_62) | ~m1_subset_1(D_62, A_59) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_2(C_61, A_59, B_60) | ~v1_funct_1(C_61) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.28  tff(c_211, plain, (![B_60, C_61]: (k3_funct_2('#skF_2', B_60, C_61, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_61, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_60))) | ~v1_funct_2(C_61, '#skF_2', B_60) | ~v1_funct_1(C_61) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_169, c_207])).
% 2.18/1.28  tff(c_224, plain, (![B_63, C_64]: (k3_funct_2('#skF_2', B_63, C_64, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_64, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_63))) | ~v1_funct_2(C_64, '#skF_2', B_63) | ~v1_funct_1(C_64))), inference(negUnitSimplification, [status(thm)], [c_42, c_211])).
% 2.18/1.28  tff(c_231, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_224])).
% 2.18/1.28  tff(c_235, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_184, c_231])).
% 2.18/1.28  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_235])).
% 2.18/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  Inference rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Ref     : 0
% 2.18/1.28  #Sup     : 38
% 2.18/1.28  #Fact    : 0
% 2.18/1.28  #Define  : 0
% 2.18/1.28  #Split   : 4
% 2.18/1.28  #Chain   : 0
% 2.18/1.28  #Close   : 0
% 2.18/1.28  
% 2.18/1.28  Ordering : KBO
% 2.18/1.28  
% 2.18/1.28  Simplification rules
% 2.18/1.28  ----------------------
% 2.18/1.28  #Subsume      : 8
% 2.18/1.28  #Demod        : 44
% 2.18/1.28  #Tautology    : 17
% 2.18/1.28  #SimpNegUnit  : 8
% 2.18/1.28  #BackRed      : 2
% 2.18/1.28  
% 2.18/1.28  #Partial instantiations: 0
% 2.18/1.28  #Strategies tried      : 1
% 2.18/1.28  
% 2.18/1.28  Timing (in seconds)
% 2.18/1.28  ----------------------
% 2.18/1.28  Preprocessing        : 0.32
% 2.18/1.28  Parsing              : 0.17
% 2.18/1.28  CNF conversion       : 0.02
% 2.18/1.28  Main loop            : 0.18
% 2.18/1.28  Inferencing          : 0.06
% 2.18/1.28  Reduction            : 0.06
% 2.18/1.28  Demodulation         : 0.04
% 2.18/1.28  BG Simplification    : 0.01
% 2.18/1.28  Subsumption          : 0.03
% 2.18/1.28  Abstraction          : 0.01
% 2.18/1.28  MUC search           : 0.00
% 2.18/1.28  Cooper               : 0.00
% 2.18/1.28  Total                : 0.54
% 2.18/1.28  Index Insertion      : 0.00
% 2.18/1.28  Index Deletion       : 0.00
% 2.18/1.28  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
