%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:55 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 302 expanded)
%              Number of leaves         :   43 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :  254 (1082 expanded)
%              Number of equality atoms :   50 ( 206 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_217,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_229,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_217])).

tff(c_38,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_248,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_38])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_522,plain,(
    ! [C_162,F_158,B_159,D_161,A_160,E_163] :
      ( k1_funct_1(k8_funct_2(B_159,C_162,A_160,D_161,E_163),F_158) = k1_funct_1(E_163,k1_funct_1(D_161,F_158))
      | k1_xboole_0 = B_159
      | ~ r1_tarski(k2_relset_1(B_159,C_162,D_161),k1_relset_1(C_162,A_160,E_163))
      | ~ m1_subset_1(F_158,B_159)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(C_162,A_160)))
      | ~ v1_funct_1(E_163)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_159,C_162)))
      | ~ v1_funct_2(D_161,B_159,C_162)
      | ~ v1_funct_1(D_161)
      | v1_xboole_0(C_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_526,plain,(
    ! [B_159,D_161,F_158] :
      ( k1_funct_1(k8_funct_2(B_159,'#skF_5','#skF_3',D_161,'#skF_7'),F_158) = k1_funct_1('#skF_7',k1_funct_1(D_161,F_158))
      | k1_xboole_0 = B_159
      | ~ r1_tarski(k2_relset_1(B_159,'#skF_5',D_161),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_158,B_159)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_159,'#skF_5')))
      | ~ v1_funct_2(D_161,B_159,'#skF_5')
      | ~ v1_funct_1(D_161)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_522])).

tff(c_532,plain,(
    ! [B_159,D_161,F_158] :
      ( k1_funct_1(k8_funct_2(B_159,'#skF_5','#skF_3',D_161,'#skF_7'),F_158) = k1_funct_1('#skF_7',k1_funct_1(D_161,F_158))
      | k1_xboole_0 = B_159
      | ~ r1_tarski(k2_relset_1(B_159,'#skF_5',D_161),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_158,B_159)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_159,'#skF_5')))
      | ~ v1_funct_2(D_161,B_159,'#skF_5')
      | ~ v1_funct_1(D_161)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_526])).

tff(c_551,plain,(
    ! [B_169,D_170,F_171] :
      ( k1_funct_1(k8_funct_2(B_169,'#skF_5','#skF_3',D_170,'#skF_7'),F_171) = k1_funct_1('#skF_7',k1_funct_1(D_170,F_171))
      | k1_xboole_0 = B_169
      | ~ r1_tarski(k2_relset_1(B_169,'#skF_5',D_170),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_171,B_169)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(B_169,'#skF_5')))
      | ~ v1_funct_2(D_170,B_169,'#skF_5')
      | ~ v1_funct_1(D_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_532])).

tff(c_553,plain,(
    ! [F_171] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_171) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_171))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_171,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_248,c_551])).

tff(c_556,plain,(
    ! [F_171] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_171) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_171))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_171,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_553])).

tff(c_557,plain,(
    ! [F_171] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_171) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_171))
      | ~ m1_subset_1(F_171,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_556])).

tff(c_18,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_59])).

tff(c_72,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_62])).

tff(c_148,plain,(
    ! [C_89,B_90,A_91] :
      ( v5_relat_1(C_89,B_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_159,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_148])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_231,plain,(
    ! [A_113,B_114,C_115] :
      ( k7_partfun1(A_113,B_114,C_115) = k1_funct_1(B_114,C_115)
      | ~ r2_hidden(C_115,k1_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v5_relat_1(B_114,A_113)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_570,plain,(
    ! [A_173,B_174,A_175] :
      ( k7_partfun1(A_173,B_174,A_175) = k1_funct_1(B_174,A_175)
      | ~ v1_funct_1(B_174)
      | ~ v5_relat_1(B_174,A_173)
      | ~ v1_relat_1(B_174)
      | v1_xboole_0(k1_relat_1(B_174))
      | ~ m1_subset_1(A_175,k1_relat_1(B_174)) ) ),
    inference(resolution,[status(thm)],[c_14,c_231])).

tff(c_576,plain,(
    ! [A_175] :
      ( k7_partfun1('#skF_5','#skF_6',A_175) = k1_funct_1('#skF_6',A_175)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_175,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_159,c_570])).

tff(c_583,plain,(
    ! [A_175] :
      ( k7_partfun1('#skF_5','#skF_6',A_175) = k1_funct_1('#skF_6',A_175)
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_175,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_50,c_576])).

tff(c_631,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_635,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_631,c_8])).

tff(c_228,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_217])).

tff(c_528,plain,(
    ! [B_159,D_161,F_158] :
      ( k1_funct_1(k8_funct_2(B_159,'#skF_4','#skF_5',D_161,'#skF_6'),F_158) = k1_funct_1('#skF_6',k1_funct_1(D_161,F_158))
      | k1_xboole_0 = B_159
      | ~ r1_tarski(k2_relset_1(B_159,'#skF_4',D_161),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_158,B_159)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_159,'#skF_4')))
      | ~ v1_funct_2(D_161,B_159,'#skF_4')
      | ~ v1_funct_1(D_161)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_522])).

tff(c_535,plain,(
    ! [B_159,D_161,F_158] :
      ( k1_funct_1(k8_funct_2(B_159,'#skF_4','#skF_5',D_161,'#skF_6'),F_158) = k1_funct_1('#skF_6',k1_funct_1(D_161,F_158))
      | k1_xboole_0 = B_159
      | ~ r1_tarski(k2_relset_1(B_159,'#skF_4',D_161),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_158,B_159)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_159,'#skF_4')))
      | ~ v1_funct_2(D_161,B_159,'#skF_4')
      | ~ v1_funct_1(D_161)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_528])).

tff(c_698,plain,(
    ! [B_159,D_161,F_158] :
      ( k1_funct_1(k8_funct_2(B_159,'#skF_4','#skF_5',D_161,'#skF_6'),F_158) = k1_funct_1('#skF_6',k1_funct_1(D_161,F_158))
      | k1_xboole_0 = B_159
      | ~ r1_tarski(k2_relset_1(B_159,'#skF_4',D_161),k1_xboole_0)
      | ~ m1_subset_1(F_158,B_159)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(B_159,'#skF_4')))
      | ~ v1_funct_2(D_161,B_159,'#skF_4')
      | ~ v1_funct_1(D_161)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_535])).

tff(c_699,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_698])).

tff(c_702,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_699,c_8])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_702])).

tff(c_708,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_160,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_148])).

tff(c_65,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_75,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_65])).

tff(c_448,plain,(
    ! [D_142,C_143,A_144,B_145] :
      ( r2_hidden(k1_funct_1(D_142,C_143),k2_relset_1(A_144,B_145,D_142))
      | k1_xboole_0 = B_145
      | ~ r2_hidden(C_143,A_144)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2(D_142,A_144,B_145)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_742,plain,(
    ! [B_204,A_200,D_203,B_202,C_201] :
      ( r2_hidden(k1_funct_1(D_203,C_201),B_204)
      | ~ r1_tarski(k2_relset_1(A_200,B_202,D_203),B_204)
      | k1_xboole_0 = B_202
      | ~ r2_hidden(C_201,A_200)
      | ~ m1_subset_1(D_203,k1_zfmisc_1(k2_zfmisc_1(A_200,B_202)))
      | ~ v1_funct_2(D_203,A_200,B_202)
      | ~ v1_funct_1(D_203) ) ),
    inference(resolution,[status(thm)],[c_448,c_2])).

tff(c_744,plain,(
    ! [C_201] :
      ( r2_hidden(k1_funct_1('#skF_6',C_201),k1_relat_1('#skF_7'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_201,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_248,c_742])).

tff(c_750,plain,(
    ! [C_201] :
      ( r2_hidden(k1_funct_1('#skF_6',C_201),k1_relat_1('#skF_7'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_201,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_744])).

tff(c_752,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(A_76,B_77)
      | v1_xboole_0(B_77)
      | ~ m1_subset_1(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,(
    ! [B_80,A_81] :
      ( ~ r1_tarski(B_80,A_81)
      | v1_xboole_0(B_80)
      | ~ m1_subset_1(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_89,c_20])).

tff(c_118,plain,(
    ! [A_7] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_135,plain,(
    ! [A_86] : ~ m1_subset_1(A_86,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_140,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_135])).

tff(c_141,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_763,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_141])).

tff(c_768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_763])).

tff(c_780,plain,(
    ! [C_207] :
      ( r2_hidden(k1_funct_1('#skF_6',C_207),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_207,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_28,plain,(
    ! [A_25,B_26,C_28] :
      ( k7_partfun1(A_25,B_26,C_28) = k1_funct_1(B_26,C_28)
      | ~ r2_hidden(C_28,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_782,plain,(
    ! [A_25,C_207] :
      ( k7_partfun1(A_25,'#skF_7',k1_funct_1('#skF_6',C_207)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_207))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_25)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_207,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_780,c_28])).

tff(c_834,plain,(
    ! [A_219,C_220] :
      ( k7_partfun1(A_219,'#skF_7',k1_funct_1('#skF_6',C_220)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_220))
      | ~ v5_relat_1('#skF_7',A_219)
      | ~ r2_hidden(C_220,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_44,c_782])).

tff(c_34,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_840,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_34])).

tff(c_846,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_840])).

tff(c_848,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_846])).

tff(c_851,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_848])).

tff(c_854,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_851])).

tff(c_856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_708,c_854])).

tff(c_857,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_846])).

tff(c_905,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_857])).

tff(c_909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.64  
% 3.67/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.67/1.64  
% 3.67/1.64  %Foreground sorts:
% 3.67/1.64  
% 3.67/1.64  
% 3.67/1.64  %Background operators:
% 3.67/1.64  
% 3.67/1.64  
% 3.67/1.64  %Foreground operators:
% 3.67/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.67/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.67/1.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.67/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.64  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.67/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.67/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.67/1.64  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.67/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.67/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.67/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.67/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.67/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.67/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.67/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.67/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.67/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.67/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.67/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.67/1.64  
% 3.67/1.66  tff(f_143, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.67/1.66  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.67/1.66  tff(f_106, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.67/1.66  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.67/1.66  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.67/1.66  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.67/1.66  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.67/1.66  tff(f_82, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.67/1.66  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.67/1.66  tff(f_118, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.67/1.66  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.67/1.66  tff(f_41, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.67/1.66  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.67/1.66  tff(f_61, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.67/1.66  tff(c_40, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_217, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.67/1.66  tff(c_229, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_217])).
% 3.67/1.66  tff(c_38, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_248, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_38])).
% 3.67/1.66  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_522, plain, (![C_162, F_158, B_159, D_161, A_160, E_163]: (k1_funct_1(k8_funct_2(B_159, C_162, A_160, D_161, E_163), F_158)=k1_funct_1(E_163, k1_funct_1(D_161, F_158)) | k1_xboole_0=B_159 | ~r1_tarski(k2_relset_1(B_159, C_162, D_161), k1_relset_1(C_162, A_160, E_163)) | ~m1_subset_1(F_158, B_159) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(C_162, A_160))) | ~v1_funct_1(E_163) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_159, C_162))) | ~v1_funct_2(D_161, B_159, C_162) | ~v1_funct_1(D_161) | v1_xboole_0(C_162))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.67/1.66  tff(c_526, plain, (![B_159, D_161, F_158]: (k1_funct_1(k8_funct_2(B_159, '#skF_5', '#skF_3', D_161, '#skF_7'), F_158)=k1_funct_1('#skF_7', k1_funct_1(D_161, F_158)) | k1_xboole_0=B_159 | ~r1_tarski(k2_relset_1(B_159, '#skF_5', D_161), k1_relat_1('#skF_7')) | ~m1_subset_1(F_158, B_159) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_159, '#skF_5'))) | ~v1_funct_2(D_161, B_159, '#skF_5') | ~v1_funct_1(D_161) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_522])).
% 3.67/1.66  tff(c_532, plain, (![B_159, D_161, F_158]: (k1_funct_1(k8_funct_2(B_159, '#skF_5', '#skF_3', D_161, '#skF_7'), F_158)=k1_funct_1('#skF_7', k1_funct_1(D_161, F_158)) | k1_xboole_0=B_159 | ~r1_tarski(k2_relset_1(B_159, '#skF_5', D_161), k1_relat_1('#skF_7')) | ~m1_subset_1(F_158, B_159) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_159, '#skF_5'))) | ~v1_funct_2(D_161, B_159, '#skF_5') | ~v1_funct_1(D_161) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_526])).
% 3.67/1.66  tff(c_551, plain, (![B_169, D_170, F_171]: (k1_funct_1(k8_funct_2(B_169, '#skF_5', '#skF_3', D_170, '#skF_7'), F_171)=k1_funct_1('#skF_7', k1_funct_1(D_170, F_171)) | k1_xboole_0=B_169 | ~r1_tarski(k2_relset_1(B_169, '#skF_5', D_170), k1_relat_1('#skF_7')) | ~m1_subset_1(F_171, B_169) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(B_169, '#skF_5'))) | ~v1_funct_2(D_170, B_169, '#skF_5') | ~v1_funct_1(D_170))), inference(negUnitSimplification, [status(thm)], [c_52, c_532])).
% 3.67/1.66  tff(c_553, plain, (![F_171]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_171)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_171)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_171, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_248, c_551])).
% 3.67/1.66  tff(c_556, plain, (![F_171]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_171)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_171)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_171, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_553])).
% 3.67/1.66  tff(c_557, plain, (![F_171]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_171)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_171)) | ~m1_subset_1(F_171, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_556])).
% 3.67/1.66  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.67/1.66  tff(c_59, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.67/1.66  tff(c_62, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_59])).
% 3.67/1.66  tff(c_72, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_62])).
% 3.67/1.66  tff(c_148, plain, (![C_89, B_90, A_91]: (v5_relat_1(C_89, B_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.67/1.66  tff(c_159, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_148])).
% 3.67/1.66  tff(c_14, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.67/1.66  tff(c_231, plain, (![A_113, B_114, C_115]: (k7_partfun1(A_113, B_114, C_115)=k1_funct_1(B_114, C_115) | ~r2_hidden(C_115, k1_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v5_relat_1(B_114, A_113) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.67/1.66  tff(c_570, plain, (![A_173, B_174, A_175]: (k7_partfun1(A_173, B_174, A_175)=k1_funct_1(B_174, A_175) | ~v1_funct_1(B_174) | ~v5_relat_1(B_174, A_173) | ~v1_relat_1(B_174) | v1_xboole_0(k1_relat_1(B_174)) | ~m1_subset_1(A_175, k1_relat_1(B_174)))), inference(resolution, [status(thm)], [c_14, c_231])).
% 3.67/1.66  tff(c_576, plain, (![A_175]: (k7_partfun1('#skF_5', '#skF_6', A_175)=k1_funct_1('#skF_6', A_175) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_175, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_159, c_570])).
% 3.67/1.66  tff(c_583, plain, (![A_175]: (k7_partfun1('#skF_5', '#skF_6', A_175)=k1_funct_1('#skF_6', A_175) | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_175, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_50, c_576])).
% 3.67/1.66  tff(c_631, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_583])).
% 3.67/1.66  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.67/1.66  tff(c_635, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_631, c_8])).
% 3.67/1.66  tff(c_228, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_217])).
% 3.67/1.66  tff(c_528, plain, (![B_159, D_161, F_158]: (k1_funct_1(k8_funct_2(B_159, '#skF_4', '#skF_5', D_161, '#skF_6'), F_158)=k1_funct_1('#skF_6', k1_funct_1(D_161, F_158)) | k1_xboole_0=B_159 | ~r1_tarski(k2_relset_1(B_159, '#skF_4', D_161), k1_relat_1('#skF_6')) | ~m1_subset_1(F_158, B_159) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_159, '#skF_4'))) | ~v1_funct_2(D_161, B_159, '#skF_4') | ~v1_funct_1(D_161) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_522])).
% 3.67/1.66  tff(c_535, plain, (![B_159, D_161, F_158]: (k1_funct_1(k8_funct_2(B_159, '#skF_4', '#skF_5', D_161, '#skF_6'), F_158)=k1_funct_1('#skF_6', k1_funct_1(D_161, F_158)) | k1_xboole_0=B_159 | ~r1_tarski(k2_relset_1(B_159, '#skF_4', D_161), k1_relat_1('#skF_6')) | ~m1_subset_1(F_158, B_159) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_159, '#skF_4'))) | ~v1_funct_2(D_161, B_159, '#skF_4') | ~v1_funct_1(D_161) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_528])).
% 3.67/1.66  tff(c_698, plain, (![B_159, D_161, F_158]: (k1_funct_1(k8_funct_2(B_159, '#skF_4', '#skF_5', D_161, '#skF_6'), F_158)=k1_funct_1('#skF_6', k1_funct_1(D_161, F_158)) | k1_xboole_0=B_159 | ~r1_tarski(k2_relset_1(B_159, '#skF_4', D_161), k1_xboole_0) | ~m1_subset_1(F_158, B_159) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(B_159, '#skF_4'))) | ~v1_funct_2(D_161, B_159, '#skF_4') | ~v1_funct_1(D_161) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_535])).
% 3.67/1.66  tff(c_699, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_698])).
% 3.67/1.66  tff(c_702, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_699, c_8])).
% 3.67/1.66  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_702])).
% 3.67/1.66  tff(c_708, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_698])).
% 3.67/1.66  tff(c_160, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_148])).
% 3.67/1.66  tff(c_65, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_59])).
% 3.67/1.66  tff(c_75, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_65])).
% 3.67/1.66  tff(c_448, plain, (![D_142, C_143, A_144, B_145]: (r2_hidden(k1_funct_1(D_142, C_143), k2_relset_1(A_144, B_145, D_142)) | k1_xboole_0=B_145 | ~r2_hidden(C_143, A_144) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2(D_142, A_144, B_145) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.67/1.66  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.67/1.66  tff(c_742, plain, (![B_204, A_200, D_203, B_202, C_201]: (r2_hidden(k1_funct_1(D_203, C_201), B_204) | ~r1_tarski(k2_relset_1(A_200, B_202, D_203), B_204) | k1_xboole_0=B_202 | ~r2_hidden(C_201, A_200) | ~m1_subset_1(D_203, k1_zfmisc_1(k2_zfmisc_1(A_200, B_202))) | ~v1_funct_2(D_203, A_200, B_202) | ~v1_funct_1(D_203))), inference(resolution, [status(thm)], [c_448, c_2])).
% 3.67/1.66  tff(c_744, plain, (![C_201]: (r2_hidden(k1_funct_1('#skF_6', C_201), k1_relat_1('#skF_7')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_201, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_248, c_742])).
% 3.67/1.66  tff(c_750, plain, (![C_201]: (r2_hidden(k1_funct_1('#skF_6', C_201), k1_relat_1('#skF_7')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_201, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_744])).
% 3.67/1.66  tff(c_752, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_750])).
% 3.67/1.66  tff(c_12, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.67/1.66  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.67/1.66  tff(c_89, plain, (![A_76, B_77]: (r2_hidden(A_76, B_77) | v1_xboole_0(B_77) | ~m1_subset_1(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.67/1.66  tff(c_20, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.67/1.66  tff(c_106, plain, (![B_80, A_81]: (~r1_tarski(B_80, A_81) | v1_xboole_0(B_80) | ~m1_subset_1(A_81, B_80))), inference(resolution, [status(thm)], [c_89, c_20])).
% 3.67/1.66  tff(c_118, plain, (![A_7]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_106])).
% 3.67/1.66  tff(c_135, plain, (![A_86]: (~m1_subset_1(A_86, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_118])).
% 3.67/1.66  tff(c_140, plain, $false, inference(resolution, [status(thm)], [c_12, c_135])).
% 3.67/1.66  tff(c_141, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_118])).
% 3.67/1.66  tff(c_763, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_141])).
% 3.67/1.66  tff(c_768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_763])).
% 3.67/1.66  tff(c_780, plain, (![C_207]: (r2_hidden(k1_funct_1('#skF_6', C_207), k1_relat_1('#skF_7')) | ~r2_hidden(C_207, '#skF_4'))), inference(splitRight, [status(thm)], [c_750])).
% 3.67/1.66  tff(c_28, plain, (![A_25, B_26, C_28]: (k7_partfun1(A_25, B_26, C_28)=k1_funct_1(B_26, C_28) | ~r2_hidden(C_28, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.67/1.66  tff(c_782, plain, (![A_25, C_207]: (k7_partfun1(A_25, '#skF_7', k1_funct_1('#skF_6', C_207))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_207)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_25) | ~v1_relat_1('#skF_7') | ~r2_hidden(C_207, '#skF_4'))), inference(resolution, [status(thm)], [c_780, c_28])).
% 3.67/1.66  tff(c_834, plain, (![A_219, C_220]: (k7_partfun1(A_219, '#skF_7', k1_funct_1('#skF_6', C_220))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_220)) | ~v5_relat_1('#skF_7', A_219) | ~r2_hidden(C_220, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_44, c_782])).
% 3.67/1.66  tff(c_34, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.67/1.66  tff(c_840, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_834, c_34])).
% 3.67/1.66  tff(c_846, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_840])).
% 3.67/1.66  tff(c_848, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_846])).
% 3.67/1.66  tff(c_851, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_14, c_848])).
% 3.67/1.66  tff(c_854, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_851])).
% 3.67/1.66  tff(c_856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_708, c_854])).
% 3.67/1.66  tff(c_857, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_846])).
% 3.67/1.66  tff(c_905, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_557, c_857])).
% 3.67/1.66  tff(c_909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_905])).
% 3.67/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.66  
% 3.67/1.66  Inference rules
% 3.67/1.66  ----------------------
% 3.67/1.66  #Ref     : 0
% 3.67/1.66  #Sup     : 171
% 3.67/1.66  #Fact    : 0
% 3.67/1.66  #Define  : 0
% 3.67/1.66  #Split   : 13
% 3.67/1.66  #Chain   : 0
% 3.67/1.66  #Close   : 0
% 3.67/1.66  
% 3.67/1.67  Ordering : KBO
% 3.67/1.67  
% 3.67/1.67  Simplification rules
% 3.67/1.67  ----------------------
% 3.67/1.67  #Subsume      : 29
% 3.67/1.67  #Demod        : 123
% 3.67/1.67  #Tautology    : 46
% 3.67/1.67  #SimpNegUnit  : 11
% 3.67/1.67  #BackRed      : 45
% 3.67/1.67  
% 3.67/1.67  #Partial instantiations: 0
% 3.67/1.67  #Strategies tried      : 1
% 3.67/1.67  
% 3.67/1.67  Timing (in seconds)
% 3.67/1.67  ----------------------
% 3.67/1.67  Preprocessing        : 0.40
% 3.67/1.67  Parsing              : 0.19
% 3.67/1.67  CNF conversion       : 0.04
% 3.67/1.67  Main loop            : 0.48
% 3.67/1.67  Inferencing          : 0.17
% 3.67/1.67  Reduction            : 0.15
% 3.67/1.67  Demodulation         : 0.10
% 3.67/1.67  BG Simplification    : 0.03
% 3.67/1.67  Subsumption          : 0.09
% 3.67/1.67  Abstraction          : 0.02
% 3.67/1.67  MUC search           : 0.00
% 3.67/1.67  Cooper               : 0.00
% 3.67/1.67  Total                : 0.93
% 3.67/1.67  Index Insertion      : 0.00
% 3.67/1.67  Index Deletion       : 0.00
% 3.67/1.67  Index Matching       : 0.00
% 3.67/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
