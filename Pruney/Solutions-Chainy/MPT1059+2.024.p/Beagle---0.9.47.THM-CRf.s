%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:36 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 119 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 296 expanded)
%              Number of equality atoms :   39 (  76 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_118,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_77,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_82,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_86,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_47,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_47])).

tff(c_28,plain,(
    ! [B_16,A_15,C_17] :
      ( k1_xboole_0 = B_16
      | k1_relset_1(A_15,B_16,C_17) = A_15
      | ~ v1_funct_2(C_17,A_15,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_107,plain,(
    ! [B_64,A_65,C_66] :
      ( B_64 = '#skF_1'
      | k1_relset_1(A_65,B_64,C_66) = A_65
      | ~ v1_funct_2(C_66,A_65,B_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

tff(c_110,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_107])).

tff(c_113,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_86,c_110])).

tff(c_114,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_124,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_partfun1(A_67,B_68,C_69) = k1_funct_1(B_68,C_69)
      | ~ r2_hidden(C_69,k1_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v5_relat_1(B_68,A_67)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_126,plain,(
    ! [A_67,C_69] :
      ( k7_partfun1(A_67,'#skF_4',C_69) = k1_funct_1('#skF_4',C_69)
      | ~ r2_hidden(C_69,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_67)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_124])).

tff(c_133,plain,(
    ! [A_70,C_71] :
      ( k7_partfun1(A_70,'#skF_4',C_71) = k1_funct_1('#skF_4',C_71)
      | ~ r2_hidden(C_71,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42,c_126])).

tff(c_136,plain,(
    ! [A_70,A_2] :
      ( k7_partfun1(A_70,'#skF_4',A_2) = k1_funct_1('#skF_4',A_2)
      | ~ v5_relat_1('#skF_4',A_70)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_133])).

tff(c_140,plain,(
    ! [A_72,A_73] :
      ( k7_partfun1(A_72,'#skF_4',A_73) = k1_funct_1('#skF_4',A_73)
      | ~ v5_relat_1('#skF_4',A_72)
      | ~ m1_subset_1(A_73,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_136])).

tff(c_144,plain,(
    ! [A_74] :
      ( k7_partfun1('#skF_3','#skF_4',A_74) = k1_funct_1('#skF_4',A_74)
      | ~ m1_subset_1(A_74,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_81,c_140])).

tff(c_148,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_144])).

tff(c_34,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_149,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_34])).

tff(c_154,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k3_funct_2(A_75,B_76,C_77,D_78) = k1_funct_1(C_77,D_78)
      | ~ m1_subset_1(D_78,A_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_2(C_77,A_75,B_76)
      | ~ v1_funct_1(C_77)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_158,plain,(
    ! [B_76,C_77] :
      ( k3_funct_2('#skF_2',B_76,C_77,'#skF_5') = k1_funct_1(C_77,'#skF_5')
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_76)))
      | ~ v1_funct_2(C_77,'#skF_2',B_76)
      | ~ v1_funct_1(C_77)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_154])).

tff(c_163,plain,(
    ! [B_79,C_80] :
      ( k3_funct_2('#skF_2',B_79,C_80,'#skF_5') = k1_funct_1(C_80,'#skF_5')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_79)))
      | ~ v1_funct_2(C_80,'#skF_2',B_79)
      | ~ v1_funct_1(C_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_158])).

tff(c_166,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_163])).

tff(c_169,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_169])).

tff(c_172,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_179,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_44])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.42  
% 2.37/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.42  
% 2.37/1.42  %Foreground sorts:
% 2.37/1.42  
% 2.37/1.42  
% 2.37/1.42  %Background operators:
% 2.37/1.42  
% 2.37/1.42  
% 2.37/1.42  %Foreground operators:
% 2.37/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.42  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.37/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.37/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.37/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.42  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.37/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.42  
% 2.50/1.44  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.50/1.44  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 2.50/1.44  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.50/1.44  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.50/1.44  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.50/1.44  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.50/1.44  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.50/1.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.50/1.44  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.50/1.44  tff(f_85, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.50/1.44  tff(f_98, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.50/1.44  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.44  tff(c_36, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.44  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.44  tff(c_77, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.50/1.44  tff(c_81, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_77])).
% 2.50/1.44  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.44  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.50/1.44  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.50/1.44  tff(c_64, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.50/1.44  tff(c_67, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.50/1.44  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_67])).
% 2.50/1.44  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.44  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.44  tff(c_82, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.50/1.44  tff(c_86, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_82])).
% 2.50/1.44  tff(c_47, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.44  tff(c_51, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_47])).
% 2.50/1.44  tff(c_28, plain, (![B_16, A_15, C_17]: (k1_xboole_0=B_16 | k1_relset_1(A_15, B_16, C_17)=A_15 | ~v1_funct_2(C_17, A_15, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.50/1.44  tff(c_107, plain, (![B_64, A_65, C_66]: (B_64='#skF_1' | k1_relset_1(A_65, B_64, C_66)=A_65 | ~v1_funct_2(C_66, A_65, B_64) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 2.50/1.44  tff(c_110, plain, ('#skF_3'='#skF_1' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_107])).
% 2.50/1.44  tff(c_113, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_86, c_110])).
% 2.50/1.44  tff(c_114, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_113])).
% 2.50/1.44  tff(c_124, plain, (![A_67, B_68, C_69]: (k7_partfun1(A_67, B_68, C_69)=k1_funct_1(B_68, C_69) | ~r2_hidden(C_69, k1_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v5_relat_1(B_68, A_67) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.50/1.44  tff(c_126, plain, (![A_67, C_69]: (k7_partfun1(A_67, '#skF_4', C_69)=k1_funct_1('#skF_4', C_69) | ~r2_hidden(C_69, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_67) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_124])).
% 2.50/1.44  tff(c_133, plain, (![A_70, C_71]: (k7_partfun1(A_70, '#skF_4', C_71)=k1_funct_1('#skF_4', C_71) | ~r2_hidden(C_71, '#skF_2') | ~v5_relat_1('#skF_4', A_70))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42, c_126])).
% 2.50/1.44  tff(c_136, plain, (![A_70, A_2]: (k7_partfun1(A_70, '#skF_4', A_2)=k1_funct_1('#skF_4', A_2) | ~v5_relat_1('#skF_4', A_70) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_133])).
% 2.50/1.44  tff(c_140, plain, (![A_72, A_73]: (k7_partfun1(A_72, '#skF_4', A_73)=k1_funct_1('#skF_4', A_73) | ~v5_relat_1('#skF_4', A_72) | ~m1_subset_1(A_73, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_136])).
% 2.50/1.44  tff(c_144, plain, (![A_74]: (k7_partfun1('#skF_3', '#skF_4', A_74)=k1_funct_1('#skF_4', A_74) | ~m1_subset_1(A_74, '#skF_2'))), inference(resolution, [status(thm)], [c_81, c_140])).
% 2.50/1.44  tff(c_148, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_144])).
% 2.50/1.44  tff(c_34, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.44  tff(c_149, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_34])).
% 2.50/1.44  tff(c_154, plain, (![A_75, B_76, C_77, D_78]: (k3_funct_2(A_75, B_76, C_77, D_78)=k1_funct_1(C_77, D_78) | ~m1_subset_1(D_78, A_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_2(C_77, A_75, B_76) | ~v1_funct_1(C_77) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.50/1.44  tff(c_158, plain, (![B_76, C_77]: (k3_funct_2('#skF_2', B_76, C_77, '#skF_5')=k1_funct_1(C_77, '#skF_5') | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_76))) | ~v1_funct_2(C_77, '#skF_2', B_76) | ~v1_funct_1(C_77) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_154])).
% 2.50/1.44  tff(c_163, plain, (![B_79, C_80]: (k3_funct_2('#skF_2', B_79, C_80, '#skF_5')=k1_funct_1(C_80, '#skF_5') | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_79))) | ~v1_funct_2(C_80, '#skF_2', B_79) | ~v1_funct_1(C_80))), inference(negUnitSimplification, [status(thm)], [c_46, c_158])).
% 2.50/1.44  tff(c_166, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_163])).
% 2.50/1.44  tff(c_169, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_166])).
% 2.50/1.44  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_169])).
% 2.50/1.44  tff(c_172, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_113])).
% 2.50/1.44  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.50/1.44  tff(c_179, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_44])).
% 2.50/1.44  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_179])).
% 2.50/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.44  
% 2.50/1.44  Inference rules
% 2.50/1.44  ----------------------
% 2.50/1.44  #Ref     : 0
% 2.50/1.44  #Sup     : 26
% 2.50/1.44  #Fact    : 0
% 2.50/1.44  #Define  : 0
% 2.50/1.44  #Split   : 1
% 2.50/1.44  #Chain   : 0
% 2.50/1.44  #Close   : 0
% 2.50/1.44  
% 2.50/1.44  Ordering : KBO
% 2.50/1.44  
% 2.50/1.44  Simplification rules
% 2.50/1.44  ----------------------
% 2.50/1.44  #Subsume      : 0
% 2.50/1.44  #Demod        : 39
% 2.50/1.44  #Tautology    : 12
% 2.50/1.44  #SimpNegUnit  : 3
% 2.50/1.44  #BackRed      : 9
% 2.50/1.44  
% 2.50/1.44  #Partial instantiations: 0
% 2.50/1.44  #Strategies tried      : 1
% 2.50/1.44  
% 2.50/1.44  Timing (in seconds)
% 2.50/1.44  ----------------------
% 2.50/1.44  Preprocessing        : 0.45
% 2.50/1.44  Parsing              : 0.22
% 2.50/1.44  CNF conversion       : 0.03
% 2.50/1.44  Main loop            : 0.21
% 2.50/1.44  Inferencing          : 0.07
% 2.50/1.44  Reduction            : 0.07
% 2.50/1.44  Demodulation         : 0.05
% 2.50/1.44  BG Simplification    : 0.02
% 2.50/1.44  Subsumption          : 0.03
% 2.50/1.44  Abstraction          : 0.01
% 2.50/1.44  MUC search           : 0.00
% 2.57/1.44  Cooper               : 0.00
% 2.57/1.44  Total                : 0.71
% 2.57/1.44  Index Insertion      : 0.00
% 2.57/1.44  Index Deletion       : 0.00
% 2.57/1.44  Index Matching       : 0.00
% 2.57/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
