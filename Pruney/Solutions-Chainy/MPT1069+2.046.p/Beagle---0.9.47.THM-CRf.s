%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:51 EST 2020

% Result     : Theorem 9.65s
% Output     : CNFRefutation 9.65s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 231 expanded)
%              Number of leaves         :   40 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  240 ( 817 expanded)
%              Number of equality atoms :   46 ( 131 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_137,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_41,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_36,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_204,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_222,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_204])).

tff(c_34,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_227,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_34])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6103,plain,(
    ! [C_1214,F_1213,A_1212,B_1215,D_1217,E_1216] :
      ( k1_funct_1(k8_funct_2(B_1215,C_1214,A_1212,D_1217,E_1216),F_1213) = k1_funct_1(E_1216,k1_funct_1(D_1217,F_1213))
      | k1_xboole_0 = B_1215
      | ~ r1_tarski(k2_relset_1(B_1215,C_1214,D_1217),k1_relset_1(C_1214,A_1212,E_1216))
      | ~ m1_subset_1(F_1213,B_1215)
      | ~ m1_subset_1(E_1216,k1_zfmisc_1(k2_zfmisc_1(C_1214,A_1212)))
      | ~ v1_funct_1(E_1216)
      | ~ m1_subset_1(D_1217,k1_zfmisc_1(k2_zfmisc_1(B_1215,C_1214)))
      | ~ v1_funct_2(D_1217,B_1215,C_1214)
      | ~ v1_funct_1(D_1217)
      | v1_xboole_0(C_1214) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6107,plain,(
    ! [B_1215,D_1217,F_1213] :
      ( k1_funct_1(k8_funct_2(B_1215,'#skF_4','#skF_2',D_1217,'#skF_6'),F_1213) = k1_funct_1('#skF_6',k1_funct_1(D_1217,F_1213))
      | k1_xboole_0 = B_1215
      | ~ r1_tarski(k2_relset_1(B_1215,'#skF_4',D_1217),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_1213,B_1215)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_1217,k1_zfmisc_1(k2_zfmisc_1(B_1215,'#skF_4')))
      | ~ v1_funct_2(D_1217,B_1215,'#skF_4')
      | ~ v1_funct_1(D_1217)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_6103])).

tff(c_6113,plain,(
    ! [B_1215,D_1217,F_1213] :
      ( k1_funct_1(k8_funct_2(B_1215,'#skF_4','#skF_2',D_1217,'#skF_6'),F_1213) = k1_funct_1('#skF_6',k1_funct_1(D_1217,F_1213))
      | k1_xboole_0 = B_1215
      | ~ r1_tarski(k2_relset_1(B_1215,'#skF_4',D_1217),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_1213,B_1215)
      | ~ m1_subset_1(D_1217,k1_zfmisc_1(k2_zfmisc_1(B_1215,'#skF_4')))
      | ~ v1_funct_2(D_1217,B_1215,'#skF_4')
      | ~ v1_funct_1(D_1217)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6107])).

tff(c_11031,plain,(
    ! [B_1831,D_1832,F_1833] :
      ( k1_funct_1(k8_funct_2(B_1831,'#skF_4','#skF_2',D_1832,'#skF_6'),F_1833) = k1_funct_1('#skF_6',k1_funct_1(D_1832,F_1833))
      | k1_xboole_0 = B_1831
      | ~ r1_tarski(k2_relset_1(B_1831,'#skF_4',D_1832),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_1833,B_1831)
      | ~ m1_subset_1(D_1832,k1_zfmisc_1(k2_zfmisc_1(B_1831,'#skF_4')))
      | ~ v1_funct_2(D_1832,B_1831,'#skF_4')
      | ~ v1_funct_1(D_1832) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6113])).

tff(c_11033,plain,(
    ! [F_1833] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_1833) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_1833))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_1833,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_227,c_11031])).

tff(c_11036,plain,(
    ! [F_1833] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_1833) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_1833))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_1833,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_11033])).

tff(c_11037,plain,(
    ! [F_1833] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_1833) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_1833))
      | ~ m1_subset_1(F_1833,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_11036])).

tff(c_126,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_144,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_126])).

tff(c_90,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_108,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_90])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [C_85,A_86,B_87] :
      ( r2_hidden(C_85,A_86)
      | ~ r2_hidden(C_85,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_256,plain,(
    ! [A_99,A_100,B_101] :
      ( r2_hidden(A_99,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100))
      | v1_xboole_0(B_101)
      | ~ m1_subset_1(A_99,B_101) ) ),
    inference(resolution,[status(thm)],[c_10,c_183])).

tff(c_6050,plain,(
    ! [A_1204,B_1205,A_1206] :
      ( r2_hidden(A_1204,B_1205)
      | v1_xboole_0(A_1206)
      | ~ m1_subset_1(A_1204,A_1206)
      | ~ r1_tarski(A_1206,B_1205) ) ),
    inference(resolution,[status(thm)],[c_14,c_256])).

tff(c_6065,plain,(
    ! [B_1205] :
      ( r2_hidden('#skF_7',B_1205)
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski('#skF_3',B_1205) ) ),
    inference(resolution,[status(thm)],[c_36,c_6050])).

tff(c_6066,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6065])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6070,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6066,c_2])).

tff(c_6074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6070])).

tff(c_6076,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6065])).

tff(c_6042,plain,(
    ! [D_1199,C_1200,A_1201,B_1202] :
      ( r2_hidden(k1_funct_1(D_1199,C_1200),k2_relset_1(A_1201,B_1202,D_1199))
      | k1_xboole_0 = B_1202
      | ~ r2_hidden(C_1200,A_1201)
      | ~ m1_subset_1(D_1199,k1_zfmisc_1(k2_zfmisc_1(A_1201,B_1202)))
      | ~ v1_funct_2(D_1199,A_1201,B_1202)
      | ~ v1_funct_1(D_1199) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9915,plain,(
    ! [D_1706,B_1710,A_1708,C_1707,A_1709] :
      ( r2_hidden(k1_funct_1(D_1706,C_1707),A_1709)
      | ~ m1_subset_1(k2_relset_1(A_1708,B_1710,D_1706),k1_zfmisc_1(A_1709))
      | k1_xboole_0 = B_1710
      | ~ r2_hidden(C_1707,A_1708)
      | ~ m1_subset_1(D_1706,k1_zfmisc_1(k2_zfmisc_1(A_1708,B_1710)))
      | ~ v1_funct_2(D_1706,A_1708,B_1710)
      | ~ v1_funct_1(D_1706) ) ),
    inference(resolution,[status(thm)],[c_6042,c_4])).

tff(c_10960,plain,(
    ! [A_1829,C_1830,B_1828,B_1826,D_1827] :
      ( r2_hidden(k1_funct_1(D_1827,C_1830),B_1828)
      | k1_xboole_0 = B_1826
      | ~ r2_hidden(C_1830,A_1829)
      | ~ m1_subset_1(D_1827,k1_zfmisc_1(k2_zfmisc_1(A_1829,B_1826)))
      | ~ v1_funct_2(D_1827,A_1829,B_1826)
      | ~ v1_funct_1(D_1827)
      | ~ r1_tarski(k2_relset_1(A_1829,B_1826,D_1827),B_1828) ) ),
    inference(resolution,[status(thm)],[c_14,c_9915])).

tff(c_11186,plain,(
    ! [B_1850,D_1851,B_1848,A_1849,B_1847] :
      ( r2_hidden(k1_funct_1(D_1851,A_1849),B_1847)
      | k1_xboole_0 = B_1848
      | ~ m1_subset_1(D_1851,k1_zfmisc_1(k2_zfmisc_1(B_1850,B_1848)))
      | ~ v1_funct_2(D_1851,B_1850,B_1848)
      | ~ v1_funct_1(D_1851)
      | ~ r1_tarski(k2_relset_1(B_1850,B_1848,D_1851),B_1847)
      | v1_xboole_0(B_1850)
      | ~ m1_subset_1(A_1849,B_1850) ) ),
    inference(resolution,[status(thm)],[c_10,c_10960])).

tff(c_11193,plain,(
    ! [A_1849,B_1847] :
      ( r2_hidden(k1_funct_1('#skF_5',A_1849),B_1847)
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_1847)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_1849,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_11186])).

tff(c_11201,plain,(
    ! [A_1849,B_1847] :
      ( r2_hidden(k1_funct_1('#skF_5',A_1849),B_1847)
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_1847)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_1849,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_11193])).

tff(c_11202,plain,(
    ! [A_1849,B_1847] :
      ( r2_hidden(k1_funct_1('#skF_5',A_1849),B_1847)
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_1847)
      | ~ m1_subset_1(A_1849,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6076,c_11201])).

tff(c_11833,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11202])).

tff(c_6,plain,(
    ! [A_6] : v1_xboole_0('#skF_1'(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_6] : '#skF_1'(A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_11873,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11833,c_55])).

tff(c_11878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_11873])).

tff(c_11880,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11202])).

tff(c_71,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_12089,plain,(
    ! [B_1991,B_1988,A_1987,B_1990,A_1989] :
      ( r2_hidden(k1_funct_1(A_1989,A_1987),B_1988)
      | k1_xboole_0 = B_1991
      | ~ v1_funct_2(A_1989,B_1990,B_1991)
      | ~ v1_funct_1(A_1989)
      | ~ r1_tarski(k2_relset_1(B_1990,B_1991,A_1989),B_1988)
      | v1_xboole_0(B_1990)
      | ~ m1_subset_1(A_1987,B_1990)
      | ~ r1_tarski(A_1989,k2_zfmisc_1(B_1990,B_1991)) ) ),
    inference(resolution,[status(thm)],[c_14,c_11186])).

tff(c_12094,plain,(
    ! [A_1987] :
      ( r2_hidden(k1_funct_1('#skF_5',A_1987),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_1987,'#skF_3')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_227,c_12089])).

tff(c_12098,plain,(
    ! [A_1987] :
      ( r2_hidden(k1_funct_1('#skF_5',A_1987),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_1987,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46,c_44,c_12094])).

tff(c_12100,plain,(
    ! [A_1992] :
      ( r2_hidden(k1_funct_1('#skF_5',A_1992),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_1992,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6076,c_11880,c_12098])).

tff(c_24,plain,(
    ! [A_21,B_22,C_24] :
      ( k7_partfun1(A_21,B_22,C_24) = k1_funct_1(B_22,C_24)
      | ~ r2_hidden(C_24,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12104,plain,(
    ! [A_21,A_1992] :
      ( k7_partfun1(A_21,'#skF_6',k1_funct_1('#skF_5',A_1992)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_1992))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_21)
      | ~ v1_relat_1('#skF_6')
      | ~ m1_subset_1(A_1992,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12100,c_24])).

tff(c_12119,plain,(
    ! [A_1995,A_1996] :
      ( k7_partfun1(A_1995,'#skF_6',k1_funct_1('#skF_5',A_1996)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_1996))
      | ~ v5_relat_1('#skF_6',A_1995)
      | ~ m1_subset_1(A_1996,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_40,c_12104])).

tff(c_30,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_12125,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12119,c_30])).

tff(c_12131,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_144,c_12125])).

tff(c_12145,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11037,c_12131])).

tff(c_12149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:42:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.65/3.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.65/3.64  
% 9.65/3.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.65/3.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 9.65/3.64  
% 9.65/3.64  %Foreground sorts:
% 9.65/3.64  
% 9.65/3.64  
% 9.65/3.64  %Background operators:
% 9.65/3.64  
% 9.65/3.64  
% 9.65/3.64  %Foreground operators:
% 9.65/3.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.65/3.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.65/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.65/3.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.65/3.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.65/3.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.65/3.64  tff('#skF_7', type, '#skF_7': $i).
% 9.65/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.65/3.64  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 9.65/3.64  tff('#skF_5', type, '#skF_5': $i).
% 9.65/3.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.65/3.64  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 9.65/3.64  tff('#skF_6', type, '#skF_6': $i).
% 9.65/3.64  tff('#skF_2', type, '#skF_2': $i).
% 9.65/3.64  tff('#skF_3', type, '#skF_3': $i).
% 9.65/3.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.65/3.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.65/3.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.65/3.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.65/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.65/3.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.65/3.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.65/3.64  tff('#skF_4', type, '#skF_4': $i).
% 9.65/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.65/3.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.65/3.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.65/3.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.65/3.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.65/3.64  
% 9.65/3.66  tff(f_137, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 9.65/3.66  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.65/3.66  tff(f_100, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 9.65/3.66  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.65/3.66  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.65/3.66  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.65/3.66  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.65/3.66  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 9.65/3.66  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.65/3.66  tff(f_112, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 9.65/3.66  tff(f_41, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 9.65/3.66  tff(f_76, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 9.65/3.66  tff(c_36, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_204, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.65/3.66  tff(c_222, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_204])).
% 9.65/3.66  tff(c_34, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_227, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_34])).
% 9.65/3.66  tff(c_48, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_6103, plain, (![C_1214, F_1213, A_1212, B_1215, D_1217, E_1216]: (k1_funct_1(k8_funct_2(B_1215, C_1214, A_1212, D_1217, E_1216), F_1213)=k1_funct_1(E_1216, k1_funct_1(D_1217, F_1213)) | k1_xboole_0=B_1215 | ~r1_tarski(k2_relset_1(B_1215, C_1214, D_1217), k1_relset_1(C_1214, A_1212, E_1216)) | ~m1_subset_1(F_1213, B_1215) | ~m1_subset_1(E_1216, k1_zfmisc_1(k2_zfmisc_1(C_1214, A_1212))) | ~v1_funct_1(E_1216) | ~m1_subset_1(D_1217, k1_zfmisc_1(k2_zfmisc_1(B_1215, C_1214))) | ~v1_funct_2(D_1217, B_1215, C_1214) | ~v1_funct_1(D_1217) | v1_xboole_0(C_1214))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.65/3.66  tff(c_6107, plain, (![B_1215, D_1217, F_1213]: (k1_funct_1(k8_funct_2(B_1215, '#skF_4', '#skF_2', D_1217, '#skF_6'), F_1213)=k1_funct_1('#skF_6', k1_funct_1(D_1217, F_1213)) | k1_xboole_0=B_1215 | ~r1_tarski(k2_relset_1(B_1215, '#skF_4', D_1217), k1_relat_1('#skF_6')) | ~m1_subset_1(F_1213, B_1215) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_1217, k1_zfmisc_1(k2_zfmisc_1(B_1215, '#skF_4'))) | ~v1_funct_2(D_1217, B_1215, '#skF_4') | ~v1_funct_1(D_1217) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_6103])).
% 9.65/3.66  tff(c_6113, plain, (![B_1215, D_1217, F_1213]: (k1_funct_1(k8_funct_2(B_1215, '#skF_4', '#skF_2', D_1217, '#skF_6'), F_1213)=k1_funct_1('#skF_6', k1_funct_1(D_1217, F_1213)) | k1_xboole_0=B_1215 | ~r1_tarski(k2_relset_1(B_1215, '#skF_4', D_1217), k1_relat_1('#skF_6')) | ~m1_subset_1(F_1213, B_1215) | ~m1_subset_1(D_1217, k1_zfmisc_1(k2_zfmisc_1(B_1215, '#skF_4'))) | ~v1_funct_2(D_1217, B_1215, '#skF_4') | ~v1_funct_1(D_1217) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6107])).
% 9.65/3.66  tff(c_11031, plain, (![B_1831, D_1832, F_1833]: (k1_funct_1(k8_funct_2(B_1831, '#skF_4', '#skF_2', D_1832, '#skF_6'), F_1833)=k1_funct_1('#skF_6', k1_funct_1(D_1832, F_1833)) | k1_xboole_0=B_1831 | ~r1_tarski(k2_relset_1(B_1831, '#skF_4', D_1832), k1_relat_1('#skF_6')) | ~m1_subset_1(F_1833, B_1831) | ~m1_subset_1(D_1832, k1_zfmisc_1(k2_zfmisc_1(B_1831, '#skF_4'))) | ~v1_funct_2(D_1832, B_1831, '#skF_4') | ~v1_funct_1(D_1832))), inference(negUnitSimplification, [status(thm)], [c_48, c_6113])).
% 9.65/3.66  tff(c_11033, plain, (![F_1833]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_1833)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_1833)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_1833, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_227, c_11031])).
% 9.65/3.66  tff(c_11036, plain, (![F_1833]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_1833)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_1833)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_1833, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_11033])).
% 9.65/3.66  tff(c_11037, plain, (![F_1833]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_1833)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_1833)) | ~m1_subset_1(F_1833, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_32, c_11036])).
% 9.65/3.66  tff(c_126, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.65/3.66  tff(c_144, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_126])).
% 9.65/3.66  tff(c_90, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.65/3.66  tff(c_108, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_90])).
% 9.65/3.66  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.65/3.66  tff(c_10, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.65/3.66  tff(c_183, plain, (![C_85, A_86, B_87]: (r2_hidden(C_85, A_86) | ~r2_hidden(C_85, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.65/3.66  tff(c_256, plain, (![A_99, A_100, B_101]: (r2_hidden(A_99, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)) | v1_xboole_0(B_101) | ~m1_subset_1(A_99, B_101))), inference(resolution, [status(thm)], [c_10, c_183])).
% 9.65/3.66  tff(c_6050, plain, (![A_1204, B_1205, A_1206]: (r2_hidden(A_1204, B_1205) | v1_xboole_0(A_1206) | ~m1_subset_1(A_1204, A_1206) | ~r1_tarski(A_1206, B_1205))), inference(resolution, [status(thm)], [c_14, c_256])).
% 9.65/3.66  tff(c_6065, plain, (![B_1205]: (r2_hidden('#skF_7', B_1205) | v1_xboole_0('#skF_3') | ~r1_tarski('#skF_3', B_1205))), inference(resolution, [status(thm)], [c_36, c_6050])).
% 9.65/3.66  tff(c_6066, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_6065])).
% 9.65/3.66  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.65/3.66  tff(c_6070, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6066, c_2])).
% 9.65/3.66  tff(c_6074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6070])).
% 9.65/3.66  tff(c_6076, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_6065])).
% 9.65/3.66  tff(c_6042, plain, (![D_1199, C_1200, A_1201, B_1202]: (r2_hidden(k1_funct_1(D_1199, C_1200), k2_relset_1(A_1201, B_1202, D_1199)) | k1_xboole_0=B_1202 | ~r2_hidden(C_1200, A_1201) | ~m1_subset_1(D_1199, k1_zfmisc_1(k2_zfmisc_1(A_1201, B_1202))) | ~v1_funct_2(D_1199, A_1201, B_1202) | ~v1_funct_1(D_1199))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.65/3.66  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.65/3.66  tff(c_9915, plain, (![D_1706, B_1710, A_1708, C_1707, A_1709]: (r2_hidden(k1_funct_1(D_1706, C_1707), A_1709) | ~m1_subset_1(k2_relset_1(A_1708, B_1710, D_1706), k1_zfmisc_1(A_1709)) | k1_xboole_0=B_1710 | ~r2_hidden(C_1707, A_1708) | ~m1_subset_1(D_1706, k1_zfmisc_1(k2_zfmisc_1(A_1708, B_1710))) | ~v1_funct_2(D_1706, A_1708, B_1710) | ~v1_funct_1(D_1706))), inference(resolution, [status(thm)], [c_6042, c_4])).
% 9.65/3.66  tff(c_10960, plain, (![A_1829, C_1830, B_1828, B_1826, D_1827]: (r2_hidden(k1_funct_1(D_1827, C_1830), B_1828) | k1_xboole_0=B_1826 | ~r2_hidden(C_1830, A_1829) | ~m1_subset_1(D_1827, k1_zfmisc_1(k2_zfmisc_1(A_1829, B_1826))) | ~v1_funct_2(D_1827, A_1829, B_1826) | ~v1_funct_1(D_1827) | ~r1_tarski(k2_relset_1(A_1829, B_1826, D_1827), B_1828))), inference(resolution, [status(thm)], [c_14, c_9915])).
% 9.65/3.66  tff(c_11186, plain, (![B_1850, D_1851, B_1848, A_1849, B_1847]: (r2_hidden(k1_funct_1(D_1851, A_1849), B_1847) | k1_xboole_0=B_1848 | ~m1_subset_1(D_1851, k1_zfmisc_1(k2_zfmisc_1(B_1850, B_1848))) | ~v1_funct_2(D_1851, B_1850, B_1848) | ~v1_funct_1(D_1851) | ~r1_tarski(k2_relset_1(B_1850, B_1848, D_1851), B_1847) | v1_xboole_0(B_1850) | ~m1_subset_1(A_1849, B_1850))), inference(resolution, [status(thm)], [c_10, c_10960])).
% 9.65/3.66  tff(c_11193, plain, (![A_1849, B_1847]: (r2_hidden(k1_funct_1('#skF_5', A_1849), B_1847) | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_1847) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_1849, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_11186])).
% 9.65/3.66  tff(c_11201, plain, (![A_1849, B_1847]: (r2_hidden(k1_funct_1('#skF_5', A_1849), B_1847) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_1847) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_1849, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_11193])).
% 9.65/3.66  tff(c_11202, plain, (![A_1849, B_1847]: (r2_hidden(k1_funct_1('#skF_5', A_1849), B_1847) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_1847) | ~m1_subset_1(A_1849, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_6076, c_11201])).
% 9.65/3.66  tff(c_11833, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_11202])).
% 9.65/3.66  tff(c_6, plain, (![A_6]: (v1_xboole_0('#skF_1'(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.65/3.66  tff(c_50, plain, (![A_58]: (k1_xboole_0=A_58 | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.65/3.66  tff(c_54, plain, (![A_6]: ('#skF_1'(A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_50])).
% 9.65/3.66  tff(c_55, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6])).
% 9.65/3.66  tff(c_11873, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11833, c_55])).
% 9.65/3.66  tff(c_11878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_11873])).
% 9.65/3.66  tff(c_11880, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_11202])).
% 9.65/3.66  tff(c_71, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.65/3.66  tff(c_85, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_71])).
% 9.65/3.66  tff(c_12089, plain, (![B_1991, B_1988, A_1987, B_1990, A_1989]: (r2_hidden(k1_funct_1(A_1989, A_1987), B_1988) | k1_xboole_0=B_1991 | ~v1_funct_2(A_1989, B_1990, B_1991) | ~v1_funct_1(A_1989) | ~r1_tarski(k2_relset_1(B_1990, B_1991, A_1989), B_1988) | v1_xboole_0(B_1990) | ~m1_subset_1(A_1987, B_1990) | ~r1_tarski(A_1989, k2_zfmisc_1(B_1990, B_1991)))), inference(resolution, [status(thm)], [c_14, c_11186])).
% 9.65/3.66  tff(c_12094, plain, (![A_1987]: (r2_hidden(k1_funct_1('#skF_5', A_1987), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_1987, '#skF_3') | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_227, c_12089])).
% 9.65/3.66  tff(c_12098, plain, (![A_1987]: (r2_hidden(k1_funct_1('#skF_5', A_1987), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | v1_xboole_0('#skF_3') | ~m1_subset_1(A_1987, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46, c_44, c_12094])).
% 9.65/3.66  tff(c_12100, plain, (![A_1992]: (r2_hidden(k1_funct_1('#skF_5', A_1992), k1_relat_1('#skF_6')) | ~m1_subset_1(A_1992, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_6076, c_11880, c_12098])).
% 9.65/3.66  tff(c_24, plain, (![A_21, B_22, C_24]: (k7_partfun1(A_21, B_22, C_24)=k1_funct_1(B_22, C_24) | ~r2_hidden(C_24, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.65/3.66  tff(c_12104, plain, (![A_21, A_1992]: (k7_partfun1(A_21, '#skF_6', k1_funct_1('#skF_5', A_1992))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_1992)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_21) | ~v1_relat_1('#skF_6') | ~m1_subset_1(A_1992, '#skF_3'))), inference(resolution, [status(thm)], [c_12100, c_24])).
% 9.65/3.66  tff(c_12119, plain, (![A_1995, A_1996]: (k7_partfun1(A_1995, '#skF_6', k1_funct_1('#skF_5', A_1996))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_1996)) | ~v5_relat_1('#skF_6', A_1995) | ~m1_subset_1(A_1996, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_40, c_12104])).
% 9.65/3.66  tff(c_30, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.65/3.66  tff(c_12125, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12119, c_30])).
% 9.65/3.66  tff(c_12131, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_144, c_12125])).
% 9.65/3.66  tff(c_12145, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11037, c_12131])).
% 9.65/3.66  tff(c_12149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_12145])).
% 9.65/3.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.65/3.66  
% 9.65/3.66  Inference rules
% 9.65/3.66  ----------------------
% 9.65/3.66  #Ref     : 0
% 9.65/3.66  #Sup     : 2451
% 9.65/3.66  #Fact    : 0
% 9.65/3.66  #Define  : 0
% 9.65/3.66  #Split   : 175
% 9.65/3.66  #Chain   : 0
% 9.65/3.66  #Close   : 0
% 9.65/3.66  
% 9.65/3.66  Ordering : KBO
% 9.65/3.66  
% 9.65/3.66  Simplification rules
% 9.65/3.66  ----------------------
% 9.65/3.66  #Subsume      : 646
% 9.65/3.66  #Demod        : 3317
% 9.65/3.66  #Tautology    : 807
% 9.65/3.66  #SimpNegUnit  : 146
% 9.65/3.66  #BackRed      : 1223
% 9.65/3.66  
% 9.65/3.66  #Partial instantiations: 0
% 9.65/3.66  #Strategies tried      : 1
% 9.65/3.66  
% 9.65/3.66  Timing (in seconds)
% 9.65/3.66  ----------------------
% 9.65/3.67  Preprocessing        : 0.39
% 9.65/3.67  Parsing              : 0.20
% 9.65/3.67  CNF conversion       : 0.03
% 9.65/3.67  Main loop            : 2.41
% 9.65/3.67  Inferencing          : 0.72
% 9.65/3.67  Reduction            : 0.83
% 9.65/3.67  Demodulation         : 0.55
% 9.65/3.67  BG Simplification    : 0.08
% 9.65/3.67  Subsumption          : 0.59
% 9.65/3.67  Abstraction          : 0.10
% 9.65/3.67  MUC search           : 0.00
% 9.65/3.67  Cooper               : 0.00
% 9.65/3.67  Total                : 2.84
% 9.65/3.67  Index Insertion      : 0.00
% 9.65/3.67  Index Deletion       : 0.00
% 9.65/3.67  Index Matching       : 0.00
% 9.65/3.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
