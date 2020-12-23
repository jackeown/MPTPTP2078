%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:37 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 271 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 826 expanded)
%              Number of equality atoms :   54 ( 205 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_67,plain,(
    ! [C_38,B_39,A_40] :
      ( v1_xboole_0(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(B_39,A_40)))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_83,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_76,plain,(
    ! [A_41,B_42,D_43] :
      ( r2_relset_1(A_41,B_42,D_43,D_43)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_84,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_92,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_84])).

tff(c_116,plain,(
    ! [B_57,A_58,C_59] :
      ( k1_xboole_0 = B_57
      | k1_relset_1(A_58,B_57,C_59) = A_58
      | ~ v1_funct_2(C_59,A_58,B_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_128,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_92,c_122])).

tff(c_135,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_65,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_91,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_84])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_116])).

tff(c_125,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_91,c_119])).

tff(c_129,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_162,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),k1_relat_1(A_64))
      | B_65 = A_64
      | k1_relat_1(B_65) != k1_relat_1(A_64)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_168,plain,(
    ! [B_65] :
      ( r2_hidden('#skF_1'('#skF_4',B_65),'#skF_2')
      | B_65 = '#skF_4'
      | k1_relat_1(B_65) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_162])).

tff(c_187,plain,(
    ! [B_68] :
      ( r2_hidden('#skF_1'('#skF_4',B_68),'#skF_2')
      | B_68 = '#skF_4'
      | k1_relat_1(B_68) != '#skF_2'
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_46,c_129,c_168])).

tff(c_34,plain,(
    ! [E_30] :
      ( k1_funct_1('#skF_5',E_30) = k1_funct_1('#skF_4',E_30)
      | ~ r2_hidden(E_30,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_191,plain,(
    ! [B_68] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_68)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_68))
      | B_68 = '#skF_4'
      | k1_relat_1(B_68) != '#skF_2'
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_187,c_34])).

tff(c_206,plain,(
    ! [B_70,A_71] :
      ( k1_funct_1(B_70,'#skF_1'(A_71,B_70)) != k1_funct_1(A_71,'#skF_1'(A_71,B_70))
      | B_70 = A_71
      | k1_relat_1(B_70) != k1_relat_1(A_71)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_210,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_206])).

tff(c_216,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_40,c_135,c_65,c_46,c_135,c_129,c_210])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_228,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_32])).

tff(c_238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_228])).

tff(c_239,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_248,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_2])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_248])).

tff(c_251,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_273,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_2])).

tff(c_275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_273])).

tff(c_276,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_47,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_2,c_47])).

tff(c_283,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_276,c_50])).

tff(c_277,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_290,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_277,c_50])).

tff(c_308,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_290])).

tff(c_343,plain,(
    r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_81])).

tff(c_75,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_67])).

tff(c_293,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_75])).

tff(c_299,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_293,c_50])).

tff(c_320,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_299])).

tff(c_312,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_32])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_320,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  
% 2.24/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.24/1.31  
% 2.24/1.31  %Foreground sorts:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Background operators:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Foreground operators:
% 2.24/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.24/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.31  
% 2.62/1.33  tff(f_114, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 2.62/1.33  tff(f_63, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.62/1.33  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.62/1.33  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.33  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.33  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.62/1.33  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 2.62/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.62/1.33  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.62/1.33  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_67, plain, (![C_38, B_39, A_40]: (v1_xboole_0(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(B_39, A_40))) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.33  tff(c_74, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_67])).
% 2.62/1.33  tff(c_83, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_74])).
% 2.62/1.33  tff(c_76, plain, (![A_41, B_42, D_43]: (r2_relset_1(A_41, B_42, D_43, D_43) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.62/1.33  tff(c_81, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_76])).
% 2.62/1.33  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_58, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.33  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_58])).
% 2.62/1.33  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_84, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.62/1.33  tff(c_92, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_84])).
% 2.62/1.33  tff(c_116, plain, (![B_57, A_58, C_59]: (k1_xboole_0=B_57 | k1_relset_1(A_58, B_57, C_59)=A_58 | ~v1_funct_2(C_59, A_58, B_57) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.62/1.33  tff(c_122, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_116])).
% 2.62/1.33  tff(c_128, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_92, c_122])).
% 2.62/1.33  tff(c_135, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_128])).
% 2.62/1.33  tff(c_65, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.62/1.33  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_91, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_84])).
% 2.62/1.33  tff(c_119, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_116])).
% 2.62/1.33  tff(c_125, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_91, c_119])).
% 2.62/1.33  tff(c_129, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_125])).
% 2.62/1.33  tff(c_162, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), k1_relat_1(A_64)) | B_65=A_64 | k1_relat_1(B_65)!=k1_relat_1(A_64) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.62/1.33  tff(c_168, plain, (![B_65]: (r2_hidden('#skF_1'('#skF_4', B_65), '#skF_2') | B_65='#skF_4' | k1_relat_1(B_65)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_65) | ~v1_relat_1(B_65) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_162])).
% 2.62/1.33  tff(c_187, plain, (![B_68]: (r2_hidden('#skF_1'('#skF_4', B_68), '#skF_2') | B_68='#skF_4' | k1_relat_1(B_68)!='#skF_2' | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_46, c_129, c_168])).
% 2.62/1.33  tff(c_34, plain, (![E_30]: (k1_funct_1('#skF_5', E_30)=k1_funct_1('#skF_4', E_30) | ~r2_hidden(E_30, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_191, plain, (![B_68]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_68))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_68)) | B_68='#skF_4' | k1_relat_1(B_68)!='#skF_2' | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_187, c_34])).
% 2.62/1.33  tff(c_206, plain, (![B_70, A_71]: (k1_funct_1(B_70, '#skF_1'(A_71, B_70))!=k1_funct_1(A_71, '#skF_1'(A_71, B_70)) | B_70=A_71 | k1_relat_1(B_70)!=k1_relat_1(A_71) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.62/1.33  tff(c_210, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_191, c_206])).
% 2.62/1.33  tff(c_216, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_40, c_135, c_65, c_46, c_135, c_129, c_210])).
% 2.62/1.33  tff(c_32, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_228, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_32])).
% 2.62/1.33  tff(c_238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_228])).
% 2.62/1.33  tff(c_239, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_128])).
% 2.62/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.62/1.33  tff(c_248, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_2])).
% 2.62/1.33  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_248])).
% 2.62/1.33  tff(c_251, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_125])).
% 2.62/1.33  tff(c_273, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_2])).
% 2.62/1.33  tff(c_275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_273])).
% 2.62/1.33  tff(c_276, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 2.62/1.33  tff(c_47, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.62/1.33  tff(c_50, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_2, c_47])).
% 2.62/1.33  tff(c_283, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_276, c_50])).
% 2.62/1.33  tff(c_277, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_74])).
% 2.62/1.33  tff(c_290, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_277, c_50])).
% 2.62/1.33  tff(c_308, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_290])).
% 2.62/1.33  tff(c_343, plain, (r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_81])).
% 2.62/1.33  tff(c_75, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_67])).
% 2.62/1.33  tff(c_293, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_75])).
% 2.62/1.33  tff(c_299, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_293, c_50])).
% 2.62/1.33  tff(c_320, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_299])).
% 2.62/1.33  tff(c_312, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_32])).
% 2.62/1.33  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_320, c_312])).
% 2.62/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  Inference rules
% 2.62/1.33  ----------------------
% 2.62/1.33  #Ref     : 1
% 2.62/1.33  #Sup     : 53
% 2.62/1.33  #Fact    : 0
% 2.62/1.33  #Define  : 0
% 2.62/1.33  #Split   : 3
% 2.62/1.33  #Chain   : 0
% 2.62/1.33  #Close   : 0
% 2.62/1.33  
% 2.62/1.33  Ordering : KBO
% 2.62/1.33  
% 2.62/1.33  Simplification rules
% 2.62/1.33  ----------------------
% 2.62/1.33  #Subsume      : 5
% 2.62/1.33  #Demod        : 124
% 2.62/1.33  #Tautology    : 47
% 2.62/1.33  #SimpNegUnit  : 2
% 2.62/1.33  #BackRed      : 38
% 2.62/1.33  
% 2.62/1.33  #Partial instantiations: 0
% 2.62/1.33  #Strategies tried      : 1
% 2.62/1.33  
% 2.62/1.33  Timing (in seconds)
% 2.62/1.33  ----------------------
% 2.62/1.33  Preprocessing        : 0.31
% 2.62/1.33  Parsing              : 0.16
% 2.62/1.33  CNF conversion       : 0.02
% 2.62/1.33  Main loop            : 0.23
% 2.62/1.33  Inferencing          : 0.08
% 2.62/1.33  Reduction            : 0.08
% 2.62/1.33  Demodulation         : 0.05
% 2.62/1.33  BG Simplification    : 0.02
% 2.62/1.33  Subsumption          : 0.04
% 2.62/1.33  Abstraction          : 0.01
% 2.62/1.33  MUC search           : 0.00
% 2.62/1.33  Cooper               : 0.00
% 2.62/1.33  Total                : 0.58
% 2.62/1.33  Index Insertion      : 0.00
% 2.62/1.33  Index Deletion       : 0.00
% 2.62/1.33  Index Matching       : 0.00
% 2.62/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
