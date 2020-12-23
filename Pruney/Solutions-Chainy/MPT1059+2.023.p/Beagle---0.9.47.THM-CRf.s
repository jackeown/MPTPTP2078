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
% DateTime   : Thu Dec  3 10:17:36 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 106 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 274 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    m1_subset_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_59,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_59])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_46])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_49])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_64,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_77,plain,(
    ! [B_58,A_59,C_60] :
      ( k1_xboole_0 = B_58
      | k1_relset_1(A_59,B_58,C_60) = A_59
      | ~ v1_funct_2(C_60,A_59,B_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_83,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_68,c_80])).

tff(c_84,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_100,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_partfun1(A_64,B_65,C_66) = k1_funct_1(B_65,C_66)
      | ~ r2_hidden(C_66,k1_relat_1(B_65))
      | ~ v1_funct_1(B_65)
      | ~ v5_relat_1(B_65,A_64)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_102,plain,(
    ! [A_64,C_66] :
      ( k7_partfun1(A_64,'#skF_3',C_66) = k1_funct_1('#skF_3',C_66)
      | ~ r2_hidden(C_66,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_64)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_100])).

tff(c_109,plain,(
    ! [A_67,C_68] :
      ( k7_partfun1(A_67,'#skF_3',C_68) = k1_funct_1('#skF_3',C_68)
      | ~ r2_hidden(C_68,'#skF_1')
      | ~ v5_relat_1('#skF_3',A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_40,c_102])).

tff(c_112,plain,(
    ! [A_67,A_1] :
      ( k7_partfun1(A_67,'#skF_3',A_1) = k1_funct_1('#skF_3',A_1)
      | ~ v5_relat_1('#skF_3',A_67)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_1,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_116,plain,(
    ! [A_69,A_70] :
      ( k7_partfun1(A_69,'#skF_3',A_70) = k1_funct_1('#skF_3',A_70)
      | ~ v5_relat_1('#skF_3',A_69)
      | ~ m1_subset_1(A_70,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_112])).

tff(c_120,plain,(
    ! [A_71] :
      ( k7_partfun1('#skF_2','#skF_3',A_71) = k1_funct_1('#skF_3',A_71)
      | ~ m1_subset_1(A_71,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_63,c_116])).

tff(c_124,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_120])).

tff(c_32,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k7_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_125,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_32])).

tff(c_137,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k3_funct_2(A_75,B_76,C_77,D_78) = k1_funct_1(C_77,D_78)
      | ~ m1_subset_1(D_78,A_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_2(C_77,A_75,B_76)
      | ~ v1_funct_1(C_77)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_141,plain,(
    ! [B_76,C_77] :
      ( k3_funct_2('#skF_1',B_76,C_77,'#skF_4') = k1_funct_1(C_77,'#skF_4')
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_76)))
      | ~ v1_funct_2(C_77,'#skF_1',B_76)
      | ~ v1_funct_1(C_77)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_137])).

tff(c_146,plain,(
    ! [B_79,C_80] :
      ( k3_funct_2('#skF_1',B_79,C_80,'#skF_4') = k1_funct_1(C_80,'#skF_4')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_79)))
      | ~ v1_funct_2(C_80,'#skF_1',B_79)
      | ~ v1_funct_1(C_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_141])).

tff(c_149,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_146])).

tff(c_152,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_149])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_152])).

tff(c_155,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_162,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:51:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.27  
% 2.28/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.28  
% 2.28/1.28  %Foreground sorts:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Background operators:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Foreground operators:
% 2.28/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.28  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.28/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.28/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.28  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.28/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.28  
% 2.28/1.29  tff(f_113, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 2.28/1.29  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.28/1.29  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.28/1.29  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.28/1.29  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.28/1.29  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.28/1.29  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.28/1.29  tff(f_80, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.28/1.29  tff(f_93, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.28/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.28/1.29  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.28/1.29  tff(c_34, plain, (m1_subset_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.28/1.29  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.28/1.29  tff(c_59, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.29  tff(c_63, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_59])).
% 2.28/1.29  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.28/1.29  tff(c_4, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.29  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.29  tff(c_46, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.29  tff(c_49, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_46])).
% 2.28/1.29  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_49])).
% 2.28/1.29  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.28/1.29  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.28/1.29  tff(c_64, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.29  tff(c_68, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_64])).
% 2.28/1.29  tff(c_77, plain, (![B_58, A_59, C_60]: (k1_xboole_0=B_58 | k1_relset_1(A_59, B_58, C_60)=A_59 | ~v1_funct_2(C_60, A_59, B_58) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.28/1.29  tff(c_80, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_77])).
% 2.28/1.29  tff(c_83, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_68, c_80])).
% 2.28/1.29  tff(c_84, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_83])).
% 2.28/1.29  tff(c_100, plain, (![A_64, B_65, C_66]: (k7_partfun1(A_64, B_65, C_66)=k1_funct_1(B_65, C_66) | ~r2_hidden(C_66, k1_relat_1(B_65)) | ~v1_funct_1(B_65) | ~v5_relat_1(B_65, A_64) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.28/1.29  tff(c_102, plain, (![A_64, C_66]: (k7_partfun1(A_64, '#skF_3', C_66)=k1_funct_1('#skF_3', C_66) | ~r2_hidden(C_66, '#skF_1') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_64) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_100])).
% 2.28/1.29  tff(c_109, plain, (![A_67, C_68]: (k7_partfun1(A_67, '#skF_3', C_68)=k1_funct_1('#skF_3', C_68) | ~r2_hidden(C_68, '#skF_1') | ~v5_relat_1('#skF_3', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_40, c_102])).
% 2.28/1.29  tff(c_112, plain, (![A_67, A_1]: (k7_partfun1(A_67, '#skF_3', A_1)=k1_funct_1('#skF_3', A_1) | ~v5_relat_1('#skF_3', A_67) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_1, '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_109])).
% 2.28/1.29  tff(c_116, plain, (![A_69, A_70]: (k7_partfun1(A_69, '#skF_3', A_70)=k1_funct_1('#skF_3', A_70) | ~v5_relat_1('#skF_3', A_69) | ~m1_subset_1(A_70, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_112])).
% 2.28/1.29  tff(c_120, plain, (![A_71]: (k7_partfun1('#skF_2', '#skF_3', A_71)=k1_funct_1('#skF_3', A_71) | ~m1_subset_1(A_71, '#skF_1'))), inference(resolution, [status(thm)], [c_63, c_116])).
% 2.28/1.29  tff(c_124, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_120])).
% 2.28/1.29  tff(c_32, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k7_partfun1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.28/1.29  tff(c_125, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_32])).
% 2.28/1.29  tff(c_137, plain, (![A_75, B_76, C_77, D_78]: (k3_funct_2(A_75, B_76, C_77, D_78)=k1_funct_1(C_77, D_78) | ~m1_subset_1(D_78, A_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_2(C_77, A_75, B_76) | ~v1_funct_1(C_77) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.28/1.29  tff(c_141, plain, (![B_76, C_77]: (k3_funct_2('#skF_1', B_76, C_77, '#skF_4')=k1_funct_1(C_77, '#skF_4') | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_76))) | ~v1_funct_2(C_77, '#skF_1', B_76) | ~v1_funct_1(C_77) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_137])).
% 2.28/1.29  tff(c_146, plain, (![B_79, C_80]: (k3_funct_2('#skF_1', B_79, C_80, '#skF_4')=k1_funct_1(C_80, '#skF_4') | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_79))) | ~v1_funct_2(C_80, '#skF_1', B_79) | ~v1_funct_1(C_80))), inference(negUnitSimplification, [status(thm)], [c_44, c_141])).
% 2.28/1.29  tff(c_149, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_146])).
% 2.28/1.29  tff(c_152, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_149])).
% 2.28/1.29  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_152])).
% 2.28/1.29  tff(c_155, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 2.28/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.28/1.29  tff(c_162, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2])).
% 2.28/1.29  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_162])).
% 2.28/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  Inference rules
% 2.28/1.29  ----------------------
% 2.28/1.29  #Ref     : 0
% 2.28/1.29  #Sup     : 23
% 2.28/1.29  #Fact    : 0
% 2.28/1.29  #Define  : 0
% 2.28/1.29  #Split   : 1
% 2.28/1.29  #Chain   : 0
% 2.28/1.29  #Close   : 0
% 2.28/1.29  
% 2.28/1.29  Ordering : KBO
% 2.28/1.29  
% 2.28/1.29  Simplification rules
% 2.28/1.29  ----------------------
% 2.28/1.29  #Subsume      : 1
% 2.28/1.29  #Demod        : 33
% 2.28/1.29  #Tautology    : 9
% 2.28/1.29  #SimpNegUnit  : 5
% 2.28/1.29  #BackRed      : 8
% 2.28/1.29  
% 2.28/1.29  #Partial instantiations: 0
% 2.28/1.29  #Strategies tried      : 1
% 2.28/1.29  
% 2.28/1.29  Timing (in seconds)
% 2.28/1.29  ----------------------
% 2.28/1.30  Preprocessing        : 0.33
% 2.28/1.30  Parsing              : 0.17
% 2.28/1.30  CNF conversion       : 0.02
% 2.28/1.30  Main loop            : 0.18
% 2.28/1.30  Inferencing          : 0.06
% 2.28/1.30  Reduction            : 0.06
% 2.28/1.30  Demodulation         : 0.04
% 2.28/1.30  BG Simplification    : 0.01
% 2.28/1.30  Subsumption          : 0.03
% 2.28/1.30  Abstraction          : 0.01
% 2.28/1.30  MUC search           : 0.00
% 2.28/1.30  Cooper               : 0.00
% 2.28/1.30  Total                : 0.54
% 2.28/1.30  Index Insertion      : 0.00
% 2.28/1.30  Index Deletion       : 0.00
% 2.28/1.30  Index Matching       : 0.00
% 2.28/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
