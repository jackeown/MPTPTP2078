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
% DateTime   : Thu Dec  3 10:12:55 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :  146 (3831 expanded)
%              Number of leaves         :   33 (1422 expanded)
%              Depth                    :   19
%              Number of atoms          :  449 (23770 expanded)
%              Number of equality atoms :  187 (9765 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & v2_funct_1(C)
                & ! [E,F] :
                    ( ( ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F )
                     => ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E ) )
                    & ( ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E )
                     => ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F ) ) ) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_84,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_84])).

tff(c_93,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_90,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_84])).

tff(c_96,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_149,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_152,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_149])).

tff(c_157,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_152])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_131,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_131])).

tff(c_171,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_177,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_6','#skF_5','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_171])).

tff(c_184,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_139,c_177])).

tff(c_185,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_184])).

tff(c_341,plain,(
    ! [A_79,B_80] :
      ( k1_funct_1(A_79,'#skF_2'(A_79,B_80)) = '#skF_1'(A_79,B_80)
      | r2_hidden('#skF_3'(A_79,B_80),k2_relat_1(A_79))
      | k2_funct_1(A_79) = B_80
      | k2_relat_1(A_79) != k1_relat_1(B_80)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80)
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_344,plain,(
    ! [B_80] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_80)) = '#skF_1'('#skF_7',B_80)
      | r2_hidden('#skF_3'('#skF_7',B_80),'#skF_6')
      | k2_funct_1('#skF_7') = B_80
      | k2_relat_1('#skF_7') != k1_relat_1(B_80)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_341])).

tff(c_346,plain,(
    ! [B_80] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_80)) = '#skF_1'('#skF_7',B_80)
      | r2_hidden('#skF_3'('#skF_7',B_80),'#skF_6')
      | k2_funct_1('#skF_7') = B_80
      | k1_relat_1(B_80) != '#skF_6'
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_157,c_344])).

tff(c_434,plain,(
    ! [A_86,B_87] :
      ( k1_funct_1(A_86,'#skF_2'(A_86,B_87)) = '#skF_1'(A_86,B_87)
      | k1_funct_1(B_87,'#skF_3'(A_86,B_87)) = '#skF_4'(A_86,B_87)
      | k2_funct_1(A_86) = B_87
      | k2_relat_1(A_86) != k1_relat_1(B_87)
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87)
      | ~ v2_funct_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ! [E_39] :
      ( r2_hidden(k1_funct_1('#skF_8',E_39),'#skF_5')
      | ~ r2_hidden(E_39,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_503,plain,(
    ! [A_86] :
      ( r2_hidden('#skF_4'(A_86,'#skF_8'),'#skF_5')
      | ~ r2_hidden('#skF_3'(A_86,'#skF_8'),'#skF_6')
      | k1_funct_1(A_86,'#skF_2'(A_86,'#skF_8')) = '#skF_1'(A_86,'#skF_8')
      | k2_funct_1(A_86) = '#skF_8'
      | k2_relat_1(A_86) != k1_relat_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ v2_funct_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_74])).

tff(c_617,plain,(
    ! [A_90] :
      ( r2_hidden('#skF_4'(A_90,'#skF_8'),'#skF_5')
      | ~ r2_hidden('#skF_3'(A_90,'#skF_8'),'#skF_6')
      | k1_funct_1(A_90,'#skF_2'(A_90,'#skF_8')) = '#skF_1'(A_90,'#skF_8')
      | k2_funct_1(A_90) = '#skF_8'
      | k2_relat_1(A_90) != '#skF_6'
      | ~ v2_funct_1(A_90)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_185,c_503])).

tff(c_620,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k2_relat_1('#skF_7') != '#skF_6'
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_346,c_617])).

tff(c_626,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_185,c_93,c_70,c_56,c_157,c_620])).

tff(c_627,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_626])).

tff(c_632,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_78,plain,(
    ! [F_40] :
      ( r2_hidden(k1_funct_1('#skF_7',F_40),'#skF_6')
      | ~ r2_hidden(F_40,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_659,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_78])).

tff(c_678,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_138,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_131])).

tff(c_174,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_171])).

tff(c_180,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_138,c_174])).

tff(c_181,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_180])).

tff(c_335,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_2'(A_77,B_78),k1_relat_1(A_77))
      | r2_hidden('#skF_3'(A_77,B_78),k2_relat_1(A_77))
      | k2_funct_1(A_77) = B_78
      | k2_relat_1(A_77) != k1_relat_1(B_78)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78)
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_338,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_2'('#skF_7',B_78),k1_relat_1('#skF_7'))
      | r2_hidden('#skF_3'('#skF_7',B_78),'#skF_6')
      | k2_funct_1('#skF_7') = B_78
      | k2_relat_1('#skF_7') != k1_relat_1(B_78)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_335])).

tff(c_340,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_2'('#skF_7',B_78),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_78),'#skF_6')
      | k2_funct_1('#skF_7') = B_78
      | k1_relat_1(B_78) != '#skF_6'
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_157,c_181,c_338])).

tff(c_349,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_2'(A_83,B_84),k1_relat_1(A_83))
      | k1_funct_1(B_84,'#skF_3'(A_83,B_84)) = '#skF_4'(A_83,B_84)
      | k2_funct_1(A_83) = B_84
      | k2_relat_1(A_83) != k1_relat_1(B_84)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_383,plain,(
    ! [B_84] :
      ( r2_hidden('#skF_2'('#skF_7',B_84),'#skF_5')
      | k1_funct_1(B_84,'#skF_3'('#skF_7',B_84)) = '#skF_4'('#skF_7',B_84)
      | k2_funct_1('#skF_7') = B_84
      | k2_relat_1('#skF_7') != k1_relat_1(B_84)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_349])).

tff(c_389,plain,(
    ! [B_84] :
      ( r2_hidden('#skF_2'('#skF_7',B_84),'#skF_5')
      | k1_funct_1(B_84,'#skF_3'('#skF_7',B_84)) = '#skF_4'('#skF_7',B_84)
      | k2_funct_1('#skF_7') = B_84
      | k1_relat_1(B_84) != '#skF_6'
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_157,c_383])).

tff(c_681,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_389,c_678])).

tff(c_684,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_185,c_681])).

tff(c_685,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_684])).

tff(c_702,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_74])).

tff(c_714,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_702])).

tff(c_720,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_340,c_714])).

tff(c_727,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_185,c_720])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_678,c_727])).

tff(c_730,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_702])).

tff(c_731,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_702])).

tff(c_72,plain,(
    ! [E_39] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_8',E_39)) = E_39
      | ~ r2_hidden(E_39,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_699,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_72])).

tff(c_740,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_699])).

tff(c_633,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_2'(A_91,B_92),k1_relat_1(A_91))
      | k1_funct_1(A_91,'#skF_4'(A_91,B_92)) != '#skF_3'(A_91,B_92)
      | ~ r2_hidden('#skF_4'(A_91,B_92),k1_relat_1(A_91))
      | k2_funct_1(A_91) = B_92
      | k2_relat_1(A_91) != k1_relat_1(B_92)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_639,plain,(
    ! [B_92] :
      ( r2_hidden('#skF_2'('#skF_7',B_92),'#skF_5')
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_92)) != '#skF_3'('#skF_7',B_92)
      | ~ r2_hidden('#skF_4'('#skF_7',B_92),k1_relat_1('#skF_7'))
      | k2_funct_1('#skF_7') = B_92
      | k2_relat_1('#skF_7') != k1_relat_1(B_92)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_633])).

tff(c_767,plain,(
    ! [B_95] :
      ( r2_hidden('#skF_2'('#skF_7',B_95),'#skF_5')
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_95)) != '#skF_3'('#skF_7',B_95)
      | ~ r2_hidden('#skF_4'('#skF_7',B_95),'#skF_5')
      | k2_funct_1('#skF_7') = B_95
      | k1_relat_1(B_95) != '#skF_6'
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_157,c_181,c_639])).

tff(c_770,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_767,c_678])).

tff(c_773,plain,(
    k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_185,c_730,c_740,c_770])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_773])).

tff(c_776,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_777,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_76,plain,(
    ! [F_40] :
      ( k1_funct_1('#skF_8',k1_funct_1('#skF_7',F_40)) = F_40
      | ~ r2_hidden(F_40,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_656,plain,
    ( k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) = '#skF_2'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_76])).

tff(c_778,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_778])).

tff(c_781,plain,(
    k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) = '#skF_2'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_18,plain,(
    ! [B_16,A_6] :
      ( k1_funct_1(B_16,'#skF_1'(A_6,B_16)) != '#skF_2'(A_6,B_16)
      | ~ r2_hidden('#skF_1'(A_6,B_16),k2_relat_1(A_6))
      | r2_hidden('#skF_3'(A_6,B_16),k2_relat_1(A_6))
      | k2_funct_1(A_6) = B_16
      | k2_relat_1(A_6) != k1_relat_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_787,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | r2_hidden('#skF_3'('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | k2_funct_1('#skF_7') = '#skF_8'
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_18])).

tff(c_804,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_96,c_64,c_157,c_185,c_157,c_776,c_157,c_787])).

tff(c_805,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_804])).

tff(c_1140,plain,(
    ! [B_109,A_110] :
      ( k1_funct_1(B_109,'#skF_1'(A_110,B_109)) != '#skF_2'(A_110,B_109)
      | ~ r2_hidden('#skF_1'(A_110,B_109),k2_relat_1(A_110))
      | k1_funct_1(B_109,'#skF_3'(A_110,B_109)) = '#skF_4'(A_110,B_109)
      | k2_funct_1(A_110) = B_109
      | k2_relat_1(A_110) != k1_relat_1(B_109)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109)
      | ~ v2_funct_1(A_110)
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1142,plain,(
    ! [B_109] :
      ( k1_funct_1(B_109,'#skF_1'('#skF_7',B_109)) != '#skF_2'('#skF_7',B_109)
      | ~ r2_hidden('#skF_1'('#skF_7',B_109),'#skF_6')
      | k1_funct_1(B_109,'#skF_3'('#skF_7',B_109)) = '#skF_4'('#skF_7',B_109)
      | k2_funct_1('#skF_7') = B_109
      | k2_relat_1('#skF_7') != k1_relat_1(B_109)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_1140])).

tff(c_1145,plain,(
    ! [B_111] :
      ( k1_funct_1(B_111,'#skF_1'('#skF_7',B_111)) != '#skF_2'('#skF_7',B_111)
      | ~ r2_hidden('#skF_1'('#skF_7',B_111),'#skF_6')
      | k1_funct_1(B_111,'#skF_3'('#skF_7',B_111)) = '#skF_4'('#skF_7',B_111)
      | k2_funct_1('#skF_7') = B_111
      | k1_relat_1(B_111) != '#skF_6'
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_157,c_1142])).

tff(c_1147,plain,
    ( k1_funct_1('#skF_8','#skF_1'('#skF_7','#skF_8')) != '#skF_2'('#skF_7','#skF_8')
    | k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_776,c_1145])).

tff(c_1152,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_185,c_781,c_1147])).

tff(c_1153,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1152])).

tff(c_1183,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_74])).

tff(c_1205,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_1183])).

tff(c_1180,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_72])).

tff(c_1203,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_1180])).

tff(c_1155,plain,(
    ! [B_112,A_113] :
      ( k1_funct_1(B_112,'#skF_1'(A_113,B_112)) != '#skF_2'(A_113,B_112)
      | ~ r2_hidden('#skF_1'(A_113,B_112),k2_relat_1(A_113))
      | k1_funct_1(A_113,'#skF_4'(A_113,B_112)) != '#skF_3'(A_113,B_112)
      | ~ r2_hidden('#skF_4'(A_113,B_112),k1_relat_1(A_113))
      | k2_funct_1(A_113) = B_112
      | k2_relat_1(A_113) != k1_relat_1(B_112)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1158,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),k1_relat_1('#skF_7'))
    | k2_funct_1('#skF_7') = '#skF_8'
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_1155])).

tff(c_1161,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_96,c_64,c_157,c_185,c_181,c_776,c_157,c_1158])).

tff(c_1162,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1161])).

tff(c_1243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1203,c_1162])).

tff(c_1245,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) != '#skF_1'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_14,plain,(
    ! [A_6,B_16] :
      ( k1_funct_1(A_6,'#skF_2'(A_6,B_16)) = '#skF_1'(A_6,B_16)
      | k1_funct_1(B_16,'#skF_3'(A_6,B_16)) = '#skF_4'(A_6,B_16)
      | k2_funct_1(A_6) = B_16
      | k2_relat_1(A_6) != k1_relat_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1248,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k2_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1245])).

tff(c_1251,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_96,c_64,c_157,c_185,c_1248])).

tff(c_1252,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_7','#skF_8')) = '#skF_4'('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1251])).

tff(c_1266,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_72])).

tff(c_1282,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1266])).

tff(c_1285,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_346,c_1282])).

tff(c_1291,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_185,c_1285])).

tff(c_1293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1245,c_1291])).

tff(c_1294,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) = '#skF_3'('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_1244,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_1771,plain,(
    ! [A_130,B_131] :
      ( k1_funct_1(A_130,'#skF_2'(A_130,B_131)) = '#skF_1'(A_130,B_131)
      | k1_funct_1(A_130,'#skF_4'(A_130,B_131)) != '#skF_3'(A_130,B_131)
      | ~ r2_hidden('#skF_4'(A_130,B_131),k1_relat_1(A_130))
      | k2_funct_1(A_130) = B_131
      | k2_relat_1(A_130) != k1_relat_1(B_131)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1777,plain,(
    ! [B_131] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_131)) = '#skF_1'('#skF_7',B_131)
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_131)) != '#skF_3'('#skF_7',B_131)
      | ~ r2_hidden('#skF_4'('#skF_7',B_131),'#skF_5')
      | k2_funct_1('#skF_7') = B_131
      | k2_relat_1('#skF_7') != k1_relat_1(B_131)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1771])).

tff(c_1784,plain,(
    ! [B_134] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_134)) = '#skF_1'('#skF_7',B_134)
      | k1_funct_1('#skF_7','#skF_4'('#skF_7',B_134)) != '#skF_3'('#skF_7',B_134)
      | ~ r2_hidden('#skF_4'('#skF_7',B_134),'#skF_5')
      | k2_funct_1('#skF_7') = B_134
      | k1_relat_1(B_134) != '#skF_6'
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_70,c_56,c_157,c_1777])).

tff(c_1787,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_8')) != '#skF_3'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1244,c_1784])).

tff(c_1790,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_8')) = '#skF_1'('#skF_7','#skF_8')
    | k2_funct_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_185,c_1294,c_1787])).

tff(c_1792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1245,c_1790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:16:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.72  
% 4.34/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.72  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.34/1.72  
% 4.34/1.72  %Foreground sorts:
% 4.34/1.72  
% 4.34/1.72  
% 4.34/1.72  %Background operators:
% 4.34/1.72  
% 4.34/1.72  
% 4.34/1.72  %Foreground operators:
% 4.34/1.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.34/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.34/1.72  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.34/1.72  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.34/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.34/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.34/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.34/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.34/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.34/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.34/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.34/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.34/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.34/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.34/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.34/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.34/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.34/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.34/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.34/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.34/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.34/1.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.34/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.34/1.72  
% 4.34/1.74  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) & (![E, F]: (((r2_hidden(E, B) & (k1_funct_1(D, E) = F)) => (r2_hidden(F, A) & (k1_funct_1(C, F) = E))) & ((r2_hidden(F, A) & (k1_funct_1(C, F) = E)) => (r2_hidden(E, B) & (k1_funct_1(D, E) = F)))))) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_2)).
% 4.34/1.74  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.34/1.74  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.34/1.74  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.34/1.74  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.34/1.74  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.34/1.74  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 4.34/1.74  tff(c_50, plain, (k2_funct_1('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.34/1.74  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_84, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.34/1.74  tff(c_87, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_84])).
% 4.34/1.74  tff(c_93, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_87])).
% 4.34/1.74  tff(c_70, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_56, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_90, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_84])).
% 4.34/1.74  tff(c_96, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_90])).
% 4.34/1.74  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_58, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_149, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.34/1.74  tff(c_152, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_149])).
% 4.34/1.74  tff(c_157, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_152])).
% 4.34/1.74  tff(c_54, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_131, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.34/1.74  tff(c_139, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_131])).
% 4.34/1.74  tff(c_171, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.34/1.74  tff(c_177, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_6', '#skF_5', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_171])).
% 4.34/1.74  tff(c_184, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_139, c_177])).
% 4.34/1.74  tff(c_185, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_54, c_184])).
% 4.34/1.74  tff(c_341, plain, (![A_79, B_80]: (k1_funct_1(A_79, '#skF_2'(A_79, B_80))='#skF_1'(A_79, B_80) | r2_hidden('#skF_3'(A_79, B_80), k2_relat_1(A_79)) | k2_funct_1(A_79)=B_80 | k2_relat_1(A_79)!=k1_relat_1(B_80) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_344, plain, (![B_80]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_80))='#skF_1'('#skF_7', B_80) | r2_hidden('#skF_3'('#skF_7', B_80), '#skF_6') | k2_funct_1('#skF_7')=B_80 | k2_relat_1('#skF_7')!=k1_relat_1(B_80) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_341])).
% 4.34/1.74  tff(c_346, plain, (![B_80]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_80))='#skF_1'('#skF_7', B_80) | r2_hidden('#skF_3'('#skF_7', B_80), '#skF_6') | k2_funct_1('#skF_7')=B_80 | k1_relat_1(B_80)!='#skF_6' | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_157, c_344])).
% 4.34/1.74  tff(c_434, plain, (![A_86, B_87]: (k1_funct_1(A_86, '#skF_2'(A_86, B_87))='#skF_1'(A_86, B_87) | k1_funct_1(B_87, '#skF_3'(A_86, B_87))='#skF_4'(A_86, B_87) | k2_funct_1(A_86)=B_87 | k2_relat_1(A_86)!=k1_relat_1(B_87) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87) | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_74, plain, (![E_39]: (r2_hidden(k1_funct_1('#skF_8', E_39), '#skF_5') | ~r2_hidden(E_39, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_503, plain, (![A_86]: (r2_hidden('#skF_4'(A_86, '#skF_8'), '#skF_5') | ~r2_hidden('#skF_3'(A_86, '#skF_8'), '#skF_6') | k1_funct_1(A_86, '#skF_2'(A_86, '#skF_8'))='#skF_1'(A_86, '#skF_8') | k2_funct_1(A_86)='#skF_8' | k2_relat_1(A_86)!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_434, c_74])).
% 4.34/1.74  tff(c_617, plain, (![A_90]: (r2_hidden('#skF_4'(A_90, '#skF_8'), '#skF_5') | ~r2_hidden('#skF_3'(A_90, '#skF_8'), '#skF_6') | k1_funct_1(A_90, '#skF_2'(A_90, '#skF_8'))='#skF_1'(A_90, '#skF_8') | k2_funct_1(A_90)='#skF_8' | k2_relat_1(A_90)!='#skF_6' | ~v2_funct_1(A_90) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_185, c_503])).
% 4.34/1.74  tff(c_620, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k2_relat_1('#skF_7')!='#skF_6' | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_346, c_617])).
% 4.34/1.74  tff(c_626, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_185, c_93, c_70, c_56, c_157, c_620])).
% 4.34/1.74  tff(c_627, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_50, c_626])).
% 4.34/1.74  tff(c_632, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_627])).
% 4.34/1.74  tff(c_78, plain, (![F_40]: (r2_hidden(k1_funct_1('#skF_7', F_40), '#skF_6') | ~r2_hidden(F_40, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_659, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_8'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_632, c_78])).
% 4.34/1.74  tff(c_678, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_659])).
% 4.34/1.74  tff(c_52, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_68, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_138, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_131])).
% 4.34/1.74  tff(c_174, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_171])).
% 4.34/1.74  tff(c_180, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_138, c_174])).
% 4.34/1.74  tff(c_181, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_52, c_180])).
% 4.34/1.74  tff(c_335, plain, (![A_77, B_78]: (r2_hidden('#skF_2'(A_77, B_78), k1_relat_1(A_77)) | r2_hidden('#skF_3'(A_77, B_78), k2_relat_1(A_77)) | k2_funct_1(A_77)=B_78 | k2_relat_1(A_77)!=k1_relat_1(B_78) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_338, plain, (![B_78]: (r2_hidden('#skF_2'('#skF_7', B_78), k1_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_7', B_78), '#skF_6') | k2_funct_1('#skF_7')=B_78 | k2_relat_1('#skF_7')!=k1_relat_1(B_78) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_335])).
% 4.34/1.74  tff(c_340, plain, (![B_78]: (r2_hidden('#skF_2'('#skF_7', B_78), '#skF_5') | r2_hidden('#skF_3'('#skF_7', B_78), '#skF_6') | k2_funct_1('#skF_7')=B_78 | k1_relat_1(B_78)!='#skF_6' | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_157, c_181, c_338])).
% 4.34/1.74  tff(c_349, plain, (![A_83, B_84]: (r2_hidden('#skF_2'(A_83, B_84), k1_relat_1(A_83)) | k1_funct_1(B_84, '#skF_3'(A_83, B_84))='#skF_4'(A_83, B_84) | k2_funct_1(A_83)=B_84 | k2_relat_1(A_83)!=k1_relat_1(B_84) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_383, plain, (![B_84]: (r2_hidden('#skF_2'('#skF_7', B_84), '#skF_5') | k1_funct_1(B_84, '#skF_3'('#skF_7', B_84))='#skF_4'('#skF_7', B_84) | k2_funct_1('#skF_7')=B_84 | k2_relat_1('#skF_7')!=k1_relat_1(B_84) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_349])).
% 4.34/1.74  tff(c_389, plain, (![B_84]: (r2_hidden('#skF_2'('#skF_7', B_84), '#skF_5') | k1_funct_1(B_84, '#skF_3'('#skF_7', B_84))='#skF_4'('#skF_7', B_84) | k2_funct_1('#skF_7')=B_84 | k1_relat_1(B_84)!='#skF_6' | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_157, c_383])).
% 4.34/1.74  tff(c_681, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_389, c_678])).
% 4.34/1.74  tff(c_684, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_185, c_681])).
% 4.34/1.74  tff(c_685, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_50, c_684])).
% 4.34/1.74  tff(c_702, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_685, c_74])).
% 4.34/1.74  tff(c_714, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_702])).
% 4.34/1.74  tff(c_720, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_340, c_714])).
% 4.34/1.74  tff(c_727, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_185, c_720])).
% 4.34/1.74  tff(c_729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_678, c_727])).
% 4.34/1.74  tff(c_730, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_702])).
% 4.34/1.74  tff(c_731, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_702])).
% 4.34/1.74  tff(c_72, plain, (![E_39]: (k1_funct_1('#skF_7', k1_funct_1('#skF_8', E_39))=E_39 | ~r2_hidden(E_39, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_699, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_685, c_72])).
% 4.34/1.74  tff(c_740, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_731, c_699])).
% 4.34/1.74  tff(c_633, plain, (![A_91, B_92]: (r2_hidden('#skF_2'(A_91, B_92), k1_relat_1(A_91)) | k1_funct_1(A_91, '#skF_4'(A_91, B_92))!='#skF_3'(A_91, B_92) | ~r2_hidden('#skF_4'(A_91, B_92), k1_relat_1(A_91)) | k2_funct_1(A_91)=B_92 | k2_relat_1(A_91)!=k1_relat_1(B_92) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_639, plain, (![B_92]: (r2_hidden('#skF_2'('#skF_7', B_92), '#skF_5') | k1_funct_1('#skF_7', '#skF_4'('#skF_7', B_92))!='#skF_3'('#skF_7', B_92) | ~r2_hidden('#skF_4'('#skF_7', B_92), k1_relat_1('#skF_7')) | k2_funct_1('#skF_7')=B_92 | k2_relat_1('#skF_7')!=k1_relat_1(B_92) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_633])).
% 4.34/1.74  tff(c_767, plain, (![B_95]: (r2_hidden('#skF_2'('#skF_7', B_95), '#skF_5') | k1_funct_1('#skF_7', '#skF_4'('#skF_7', B_95))!='#skF_3'('#skF_7', B_95) | ~r2_hidden('#skF_4'('#skF_7', B_95), '#skF_5') | k2_funct_1('#skF_7')=B_95 | k1_relat_1(B_95)!='#skF_6' | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_157, c_181, c_639])).
% 4.34/1.74  tff(c_770, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))!='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_767, c_678])).
% 4.34/1.74  tff(c_773, plain, (k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_185, c_730, c_740, c_770])).
% 4.34/1.74  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_773])).
% 4.34/1.74  tff(c_776, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_659])).
% 4.34/1.74  tff(c_777, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_659])).
% 4.34/1.74  tff(c_76, plain, (![F_40]: (k1_funct_1('#skF_8', k1_funct_1('#skF_7', F_40))=F_40 | ~r2_hidden(F_40, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.34/1.74  tff(c_656, plain, (k1_funct_1('#skF_8', '#skF_1'('#skF_7', '#skF_8'))='#skF_2'('#skF_7', '#skF_8') | ~r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_632, c_76])).
% 4.34/1.74  tff(c_778, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_656])).
% 4.34/1.74  tff(c_780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_777, c_778])).
% 4.34/1.74  tff(c_781, plain, (k1_funct_1('#skF_8', '#skF_1'('#skF_7', '#skF_8'))='#skF_2'('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_656])).
% 4.34/1.74  tff(c_18, plain, (![B_16, A_6]: (k1_funct_1(B_16, '#skF_1'(A_6, B_16))!='#skF_2'(A_6, B_16) | ~r2_hidden('#skF_1'(A_6, B_16), k2_relat_1(A_6)) | r2_hidden('#skF_3'(A_6, B_16), k2_relat_1(A_6)) | k2_funct_1(A_6)=B_16 | k2_relat_1(A_6)!=k1_relat_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_787, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_8'), k2_relat_1('#skF_7')) | r2_hidden('#skF_3'('#skF_7', '#skF_8'), k2_relat_1('#skF_7')) | k2_funct_1('#skF_7')='#skF_8' | k2_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_781, c_18])).
% 4.34/1.74  tff(c_804, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_96, c_64, c_157, c_185, c_157, c_776, c_157, c_787])).
% 4.34/1.74  tff(c_805, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_804])).
% 4.34/1.74  tff(c_1140, plain, (![B_109, A_110]: (k1_funct_1(B_109, '#skF_1'(A_110, B_109))!='#skF_2'(A_110, B_109) | ~r2_hidden('#skF_1'(A_110, B_109), k2_relat_1(A_110)) | k1_funct_1(B_109, '#skF_3'(A_110, B_109))='#skF_4'(A_110, B_109) | k2_funct_1(A_110)=B_109 | k2_relat_1(A_110)!=k1_relat_1(B_109) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109) | ~v2_funct_1(A_110) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_1142, plain, (![B_109]: (k1_funct_1(B_109, '#skF_1'('#skF_7', B_109))!='#skF_2'('#skF_7', B_109) | ~r2_hidden('#skF_1'('#skF_7', B_109), '#skF_6') | k1_funct_1(B_109, '#skF_3'('#skF_7', B_109))='#skF_4'('#skF_7', B_109) | k2_funct_1('#skF_7')=B_109 | k2_relat_1('#skF_7')!=k1_relat_1(B_109) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_1140])).
% 4.34/1.74  tff(c_1145, plain, (![B_111]: (k1_funct_1(B_111, '#skF_1'('#skF_7', B_111))!='#skF_2'('#skF_7', B_111) | ~r2_hidden('#skF_1'('#skF_7', B_111), '#skF_6') | k1_funct_1(B_111, '#skF_3'('#skF_7', B_111))='#skF_4'('#skF_7', B_111) | k2_funct_1('#skF_7')=B_111 | k1_relat_1(B_111)!='#skF_6' | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_157, c_1142])).
% 4.34/1.74  tff(c_1147, plain, (k1_funct_1('#skF_8', '#skF_1'('#skF_7', '#skF_8'))!='#skF_2'('#skF_7', '#skF_8') | k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_776, c_1145])).
% 4.34/1.74  tff(c_1152, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_185, c_781, c_1147])).
% 4.34/1.74  tff(c_1153, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_50, c_1152])).
% 4.34/1.74  tff(c_1183, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_74])).
% 4.34/1.74  tff(c_1205, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_805, c_1183])).
% 4.34/1.74  tff(c_1180, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_72])).
% 4.34/1.74  tff(c_1203, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_805, c_1180])).
% 4.34/1.74  tff(c_1155, plain, (![B_112, A_113]: (k1_funct_1(B_112, '#skF_1'(A_113, B_112))!='#skF_2'(A_113, B_112) | ~r2_hidden('#skF_1'(A_113, B_112), k2_relat_1(A_113)) | k1_funct_1(A_113, '#skF_4'(A_113, B_112))!='#skF_3'(A_113, B_112) | ~r2_hidden('#skF_4'(A_113, B_112), k1_relat_1(A_113)) | k2_funct_1(A_113)=B_112 | k2_relat_1(A_113)!=k1_relat_1(B_112) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_1158, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_8'), k2_relat_1('#skF_7')) | k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))!='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_4'('#skF_7', '#skF_8'), k1_relat_1('#skF_7')) | k2_funct_1('#skF_7')='#skF_8' | k2_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_781, c_1155])).
% 4.34/1.74  tff(c_1161, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))!='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_96, c_64, c_157, c_185, c_181, c_776, c_157, c_1158])).
% 4.34/1.74  tff(c_1162, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))!='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_1161])).
% 4.34/1.74  tff(c_1243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1203, c_1162])).
% 4.34/1.74  tff(c_1245, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))!='#skF_1'('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_627])).
% 4.34/1.74  tff(c_14, plain, (![A_6, B_16]: (k1_funct_1(A_6, '#skF_2'(A_6, B_16))='#skF_1'(A_6, B_16) | k1_funct_1(B_16, '#skF_3'(A_6, B_16))='#skF_4'(A_6, B_16) | k2_funct_1(A_6)=B_16 | k2_relat_1(A_6)!=k1_relat_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_1248, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k2_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1245])).
% 4.34/1.74  tff(c_1251, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_96, c_64, c_157, c_185, c_1248])).
% 4.34/1.74  tff(c_1252, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_7', '#skF_8'))='#skF_4'('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_50, c_1251])).
% 4.34/1.74  tff(c_1266, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8') | ~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1252, c_72])).
% 4.34/1.74  tff(c_1282, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1266])).
% 4.34/1.74  tff(c_1285, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_346, c_1282])).
% 4.34/1.74  tff(c_1291, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_185, c_1285])).
% 4.34/1.74  tff(c_1293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1245, c_1291])).
% 4.34/1.74  tff(c_1294, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))='#skF_3'('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_1266])).
% 4.34/1.74  tff(c_1244, plain, (r2_hidden('#skF_4'('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_627])).
% 4.34/1.74  tff(c_1771, plain, (![A_130, B_131]: (k1_funct_1(A_130, '#skF_2'(A_130, B_131))='#skF_1'(A_130, B_131) | k1_funct_1(A_130, '#skF_4'(A_130, B_131))!='#skF_3'(A_130, B_131) | ~r2_hidden('#skF_4'(A_130, B_131), k1_relat_1(A_130)) | k2_funct_1(A_130)=B_131 | k2_relat_1(A_130)!=k1_relat_1(B_131) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.34/1.74  tff(c_1777, plain, (![B_131]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_131))='#skF_1'('#skF_7', B_131) | k1_funct_1('#skF_7', '#skF_4'('#skF_7', B_131))!='#skF_3'('#skF_7', B_131) | ~r2_hidden('#skF_4'('#skF_7', B_131), '#skF_5') | k2_funct_1('#skF_7')=B_131 | k2_relat_1('#skF_7')!=k1_relat_1(B_131) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_1771])).
% 4.34/1.74  tff(c_1784, plain, (![B_134]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_134))='#skF_1'('#skF_7', B_134) | k1_funct_1('#skF_7', '#skF_4'('#skF_7', B_134))!='#skF_3'('#skF_7', B_134) | ~r2_hidden('#skF_4'('#skF_7', B_134), '#skF_5') | k2_funct_1('#skF_7')=B_134 | k1_relat_1(B_134)!='#skF_6' | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_70, c_56, c_157, c_1777])).
% 4.34/1.74  tff(c_1787, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_8'))!='#skF_3'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1244, c_1784])).
% 4.34/1.74  tff(c_1790, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_8'))='#skF_1'('#skF_7', '#skF_8') | k2_funct_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_185, c_1294, c_1787])).
% 4.34/1.74  tff(c_1792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1245, c_1790])).
% 4.34/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.74  
% 4.34/1.74  Inference rules
% 4.34/1.74  ----------------------
% 4.34/1.74  #Ref     : 0
% 4.34/1.74  #Sup     : 340
% 4.34/1.74  #Fact    : 0
% 4.34/1.74  #Define  : 0
% 4.34/1.74  #Split   : 9
% 4.34/1.74  #Chain   : 0
% 4.34/1.74  #Close   : 0
% 4.34/1.74  
% 4.34/1.74  Ordering : KBO
% 4.34/1.74  
% 4.34/1.74  Simplification rules
% 4.34/1.74  ----------------------
% 4.34/1.74  #Subsume      : 60
% 4.34/1.74  #Demod        : 641
% 4.34/1.74  #Tautology    : 188
% 4.34/1.74  #SimpNegUnit  : 47
% 4.34/1.74  #BackRed      : 2
% 4.34/1.74  
% 4.34/1.74  #Partial instantiations: 0
% 4.34/1.74  #Strategies tried      : 1
% 4.34/1.74  
% 4.34/1.74  Timing (in seconds)
% 4.34/1.74  ----------------------
% 4.34/1.74  Preprocessing        : 0.36
% 4.34/1.74  Parsing              : 0.17
% 4.34/1.74  CNF conversion       : 0.03
% 4.34/1.75  Main loop            : 0.64
% 4.34/1.75  Inferencing          : 0.22
% 4.34/1.75  Reduction            : 0.21
% 4.34/1.75  Demodulation         : 0.15
% 4.34/1.75  BG Simplification    : 0.04
% 4.34/1.75  Subsumption          : 0.13
% 4.34/1.75  Abstraction          : 0.04
% 4.34/1.75  MUC search           : 0.00
% 4.34/1.75  Cooper               : 0.00
% 4.34/1.75  Total                : 1.05
% 4.34/1.75  Index Insertion      : 0.00
% 4.34/1.75  Index Deletion       : 0.00
% 4.34/1.75  Index Matching       : 0.00
% 4.34/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
