%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:17 EST 2020

% Result     : Theorem 11.12s
% Output     : CNFRefutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :   85 (1693 expanded)
%              Number of leaves         :   28 ( 682 expanded)
%              Depth                    :   23
%              Number of atoms          :  329 (12214 expanded)
%              Number of equality atoms :  258 (7795 expanded)
%              Maximal formula depth    :   29 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = H ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k9_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E,F] :
      ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
     => ( ! [G] :
            ( m1_subset_1(G,A)
           => ! [H] :
                ( m1_subset_1(H,B)
               => ! [I] :
                    ( m1_subset_1(I,C)
                   => ! [J] :
                        ( m1_subset_1(J,D)
                       => ( F = k4_mcart_1(G,H,I,J)
                         => E = G ) ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | E = k8_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ? [F,G,H,I] :
              ( E = k4_mcart_1(F,G,H,I)
              & ~ ( k8_mcart_1(A,B,C,D,E) = F
                  & k9_mcart_1(A,B,C,D,E) = G
                  & k10_mcart_1(A,B,C,D,E) = H
                  & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

tff(c_26,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( k4_mcart_1('#skF_1'(A_22,C_24,E_26,F_27,D_25,B_23),'#skF_2'(A_22,C_24,E_26,F_27,D_25,B_23),'#skF_3'(A_22,C_24,E_26,F_27,D_25,B_23),'#skF_4'(A_22,C_24,E_26,F_27,D_25,B_23)) = F_27
      | k8_mcart_1(A_22,B_23,C_24,D_25,F_27) = E_26
      | k1_xboole_0 = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(F_27,k4_zfmisc_1(A_22,B_23,C_24,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_76,plain,(
    ! [D_162,C_159,B_163,A_158,F_161,E_160] :
      ( k4_mcart_1('#skF_1'(A_158,C_159,E_160,F_161,D_162,B_163),'#skF_2'(A_158,C_159,E_160,F_161,D_162,B_163),'#skF_3'(A_158,C_159,E_160,F_161,D_162,B_163),'#skF_4'(A_158,C_159,E_160,F_161,D_162,B_163)) = F_161
      | k8_mcart_1(A_158,B_163,C_159,D_162,F_161) = E_160
      | k1_xboole_0 = D_162
      | k1_xboole_0 = C_159
      | k1_xboole_0 = B_163
      | k1_xboole_0 = A_158
      | ~ m1_subset_1(F_161,k4_zfmisc_1(A_158,B_163,C_159,D_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [H_20,C_11,F_18,I_21,B_10,G_19,D_12,A_9] :
      ( k9_mcart_1(A_9,B_10,C_11,D_12,k4_mcart_1(F_18,G_19,H_20,I_21)) = G_19
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(k4_mcart_1(F_18,G_19,H_20,I_21),k4_zfmisc_1(A_9,B_10,C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_528,plain,(
    ! [D_1878,D_1874,B_1870,A_1879,F_1871,C_1876,B_1875,A_1873,C_1877,E_1872] :
      ( k9_mcart_1(A_1879,B_1875,C_1877,D_1878,k4_mcart_1('#skF_1'(A_1873,C_1876,E_1872,F_1871,D_1874,B_1870),'#skF_2'(A_1873,C_1876,E_1872,F_1871,D_1874,B_1870),'#skF_3'(A_1873,C_1876,E_1872,F_1871,D_1874,B_1870),'#skF_4'(A_1873,C_1876,E_1872,F_1871,D_1874,B_1870))) = '#skF_2'(A_1873,C_1876,E_1872,F_1871,D_1874,B_1870)
      | k1_xboole_0 = D_1878
      | k1_xboole_0 = C_1877
      | k1_xboole_0 = B_1875
      | k1_xboole_0 = A_1879
      | ~ m1_subset_1(F_1871,k4_zfmisc_1(A_1879,B_1875,C_1877,D_1878))
      | k8_mcart_1(A_1873,B_1870,C_1876,D_1874,F_1871) = E_1872
      | k1_xboole_0 = D_1874
      | k1_xboole_0 = C_1876
      | k1_xboole_0 = B_1870
      | k1_xboole_0 = A_1873
      | ~ m1_subset_1(F_1871,k4_zfmisc_1(A_1873,B_1870,C_1876,D_1874)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_10])).

tff(c_20439,plain,(
    ! [A_55902,B_55906,C_55903,D_55909,E_55904,A_55901,B_55910,F_55905,C_55907,D_55908] :
      ( k9_mcart_1(A_55902,B_55906,C_55907,D_55909,F_55905) = '#skF_2'(A_55901,C_55903,E_55904,F_55905,D_55908,B_55910)
      | k1_xboole_0 = D_55909
      | k1_xboole_0 = C_55907
      | k1_xboole_0 = B_55906
      | k1_xboole_0 = A_55902
      | ~ m1_subset_1(F_55905,k4_zfmisc_1(A_55902,B_55906,C_55907,D_55909))
      | k8_mcart_1(A_55901,B_55910,C_55903,D_55908,F_55905) = E_55904
      | k1_xboole_0 = D_55908
      | k1_xboole_0 = C_55903
      | k1_xboole_0 = B_55910
      | k1_xboole_0 = A_55901
      | ~ m1_subset_1(F_55905,k4_zfmisc_1(A_55901,B_55910,C_55903,D_55908))
      | k8_mcart_1(A_55901,B_55910,C_55903,D_55908,F_55905) = E_55904
      | k1_xboole_0 = D_55908
      | k1_xboole_0 = C_55903
      | k1_xboole_0 = B_55910
      | k1_xboole_0 = A_55901
      | ~ m1_subset_1(F_55905,k4_zfmisc_1(A_55901,B_55910,C_55903,D_55908)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_528])).

tff(c_20494,plain,(
    ! [C_55903,E_55904,A_55901,B_55910,D_55908] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_2'(A_55901,C_55903,E_55904,'#skF_10',D_55908,B_55910)
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k8_mcart_1(A_55901,B_55910,C_55903,D_55908,'#skF_10') = E_55904
      | k1_xboole_0 = D_55908
      | k1_xboole_0 = C_55903
      | k1_xboole_0 = B_55910
      | k1_xboole_0 = A_55901
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_55901,B_55910,C_55903,D_55908)) ) ),
    inference(resolution,[status(thm)],[c_38,c_20439])).

tff(c_20599,plain,(
    ! [C_56035,E_56038,D_56037,B_56036,A_56039] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_2'(A_56039,C_56035,E_56038,'#skF_10',D_56037,B_56036)
      | k8_mcart_1(A_56039,B_56036,C_56035,D_56037,'#skF_10') = E_56038
      | k1_xboole_0 = D_56037
      | k1_xboole_0 = C_56035
      | k1_xboole_0 = B_56036
      | k1_xboole_0 = A_56039
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_56039,B_56036,C_56035,D_56037)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_20494])).

tff(c_20622,plain,(
    ! [E_56038] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_2'('#skF_5','#skF_7',E_56038,'#skF_10','#skF_8','#skF_6')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_56038
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_38,c_20599])).

tff(c_20628,plain,(
    ! [E_56102] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_2'('#skF_5','#skF_7',E_56102,'#skF_10','#skF_8','#skF_6')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_56102 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_20622])).

tff(c_18,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_4'(A_22,C_24,E_26,F_27,D_25,B_23),D_25)
      | k8_mcart_1(A_22,B_23,C_24,D_25,F_27) = E_26
      | k1_xboole_0 = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(F_27,k4_zfmisc_1(A_22,B_23,C_24,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_3'(A_22,C_24,E_26,F_27,D_25,B_23),C_24)
      | k8_mcart_1(A_22,B_23,C_24,D_25,F_27) = E_26
      | k1_xboole_0 = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(F_27,k4_zfmisc_1(A_22,B_23,C_24,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_1'(A_22,C_24,E_26,F_27,D_25,B_23),A_22)
      | k8_mcart_1(A_22,B_23,C_24,D_25,F_27) = E_26
      | k1_xboole_0 = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(F_27,k4_zfmisc_1(A_22,B_23,C_24,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_2'(A_22,C_24,E_26,F_27,D_25,B_23),B_23)
      | k8_mcart_1(A_22,B_23,C_24,D_25,F_27) = E_26
      | k1_xboole_0 = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(F_27,k4_zfmisc_1(A_22,B_23,C_24,D_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [H_77,G_69,I_81,J_83] :
      ( H_77 = '#skF_9'
      | k4_mcart_1(G_69,H_77,I_81,J_83) != '#skF_10'
      | ~ m1_subset_1(J_83,'#skF_8')
      | ~ m1_subset_1(I_81,'#skF_7')
      | ~ m1_subset_1(H_77,'#skF_6')
      | ~ m1_subset_1(G_69,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_100,plain,(
    ! [C_169,E_166,A_167,D_168,B_164,F_165] :
      ( '#skF_2'(A_167,C_169,E_166,F_165,D_168,B_164) = '#skF_9'
      | F_165 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_167,C_169,E_166,F_165,D_168,B_164),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_167,C_169,E_166,F_165,D_168,B_164),'#skF_7')
      | ~ m1_subset_1('#skF_2'(A_167,C_169,E_166,F_165,D_168,B_164),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_167,C_169,E_166,F_165,D_168,B_164),'#skF_5')
      | k8_mcart_1(A_167,B_164,C_169,D_168,F_165) = E_166
      | k1_xboole_0 = D_168
      | k1_xboole_0 = C_169
      | k1_xboole_0 = B_164
      | k1_xboole_0 = A_167
      | ~ m1_subset_1(F_165,k4_zfmisc_1(A_167,B_164,C_169,D_168)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_36])).

tff(c_104,plain,(
    ! [E_26,F_27,A_22,D_25,C_24] :
      ( '#skF_2'(A_22,C_24,E_26,F_27,D_25,'#skF_6') = '#skF_9'
      | F_27 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_22,C_24,E_26,F_27,D_25,'#skF_6'),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_22,C_24,E_26,F_27,D_25,'#skF_6'),'#skF_7')
      | ~ m1_subset_1('#skF_1'(A_22,C_24,E_26,F_27,D_25,'#skF_6'),'#skF_5')
      | k8_mcart_1(A_22,'#skF_6',C_24,D_25,F_27) = E_26
      | k1_xboole_0 = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(F_27,k4_zfmisc_1(A_22,'#skF_6',C_24,D_25)) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_109,plain,(
    ! [C_171,A_170,F_173,D_174,E_172] :
      ( '#skF_2'(A_170,C_171,E_172,F_173,D_174,'#skF_6') = '#skF_9'
      | F_173 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(A_170,C_171,E_172,F_173,D_174,'#skF_6'),'#skF_8')
      | ~ m1_subset_1('#skF_3'(A_170,C_171,E_172,F_173,D_174,'#skF_6'),'#skF_7')
      | ~ m1_subset_1('#skF_1'(A_170,C_171,E_172,F_173,D_174,'#skF_6'),'#skF_5')
      | k8_mcart_1(A_170,'#skF_6',C_171,D_174,F_173) = E_172
      | k1_xboole_0 = D_174
      | k1_xboole_0 = C_171
      | k1_xboole_0 = A_170
      | ~ m1_subset_1(F_173,k4_zfmisc_1(A_170,'#skF_6',C_171,D_174)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_104])).

tff(c_113,plain,(
    ! [C_24,E_26,F_27,D_25] :
      ( '#skF_2'('#skF_5',C_24,E_26,F_27,D_25,'#skF_6') = '#skF_9'
      | F_27 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_5',C_24,E_26,F_27,D_25,'#skF_6'),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_5',C_24,E_26,F_27,D_25,'#skF_6'),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_24,D_25,F_27) = E_26
      | k1_xboole_0 = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_27,k4_zfmisc_1('#skF_5','#skF_6',C_24,D_25)) ) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_118,plain,(
    ! [C_175,E_176,F_177,D_178] :
      ( '#skF_2'('#skF_5',C_175,E_176,F_177,D_178,'#skF_6') = '#skF_9'
      | F_177 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_5',C_175,E_176,F_177,D_178,'#skF_6'),'#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_5',C_175,E_176,F_177,D_178,'#skF_6'),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_175,D_178,F_177) = E_176
      | k1_xboole_0 = D_178
      | k1_xboole_0 = C_175
      | ~ m1_subset_1(F_177,k4_zfmisc_1('#skF_5','#skF_6',C_175,D_178)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_34,c_113])).

tff(c_122,plain,(
    ! [E_26,F_27,D_25] :
      ( '#skF_2'('#skF_5','#skF_7',E_26,F_27,D_25,'#skF_6') = '#skF_9'
      | F_27 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_7',E_26,F_27,D_25,'#skF_6'),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_25,F_27) = E_26
      | k1_xboole_0 = D_25
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_27,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_25)) ) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_127,plain,(
    ! [E_179,F_180,D_181] :
      ( '#skF_2'('#skF_5','#skF_7',E_179,F_180,D_181,'#skF_6') = '#skF_9'
      | F_180 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_7',E_179,F_180,D_181,'#skF_6'),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_181,F_180) = E_179
      | k1_xboole_0 = D_181
      | ~ m1_subset_1(F_180,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_181)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_30,c_122])).

tff(c_131,plain,(
    ! [E_26,F_27] :
      ( '#skF_2'('#skF_5','#skF_7',E_26,F_27,'#skF_8','#skF_6') = '#skF_9'
      | F_27 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_27) = E_26
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_27,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_18,c_127])).

tff(c_136,plain,(
    ! [E_182,F_183] :
      ( '#skF_2'('#skF_5','#skF_7',E_182,F_183,'#skF_8','#skF_6') = '#skF_9'
      | F_183 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_183) = E_182
      | ~ m1_subset_1(F_183,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_28,c_131])).

tff(c_155,plain,(
    ! [E_182] :
      ( '#skF_2'('#skF_5','#skF_7',E_182,'#skF_10','#skF_8','#skF_6') = '#skF_9'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_182 ) ),
    inference(resolution,[status(thm)],[c_38,c_136])).

tff(c_198,plain,
    ( '#skF_2'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6') = '#skF_9'
    | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_136])).

tff(c_199,plain,(
    ! [E_182] :
      ( '#skF_2'('#skF_5','#skF_7',E_182,'#skF_10','#skF_8','#skF_6') = '#skF_9'
      | k1_xboole_0 = E_182
      | '#skF_2'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6') = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_155])).

tff(c_689,plain,(
    '#skF_2'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_82,plain,(
    ! [D_162,C_159,C_11,B_163,B_10,A_158,F_161,D_12,E_160,A_9] :
      ( k9_mcart_1(A_9,B_10,C_11,D_12,k4_mcart_1('#skF_1'(A_158,C_159,E_160,F_161,D_162,B_163),'#skF_2'(A_158,C_159,E_160,F_161,D_162,B_163),'#skF_3'(A_158,C_159,E_160,F_161,D_162,B_163),'#skF_4'(A_158,C_159,E_160,F_161,D_162,B_163))) = '#skF_2'(A_158,C_159,E_160,F_161,D_162,B_163)
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(F_161,k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k8_mcart_1(A_158,B_163,C_159,D_162,F_161) = E_160
      | k1_xboole_0 = D_162
      | k1_xboole_0 = C_159
      | k1_xboole_0 = B_163
      | k1_xboole_0 = A_158
      | ~ m1_subset_1(F_161,k4_zfmisc_1(A_158,B_163,C_159,D_162)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_10])).

tff(c_693,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k9_mcart_1(A_9,B_10,C_11,D_12,k4_mcart_1('#skF_1'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'),'#skF_9','#skF_3'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'),'#skF_4'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'))) = '#skF_2'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6')
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k1_xboole_0
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_82])).

tff(c_708,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k9_mcart_1(A_9,B_10,C_11,D_12,k4_mcart_1('#skF_1'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'),'#skF_9','#skF_3'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'),'#skF_4'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'))) = '#skF_9'
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k1_xboole_0
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_689,c_693])).

tff(c_709,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k9_mcart_1(A_9,B_10,C_11,D_12,k4_mcart_1('#skF_1'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'),'#skF_9','#skF_3'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'),'#skF_4'('#skF_5','#skF_7',k1_xboole_0,'#skF_10','#skF_8','#skF_6'))) = '#skF_9'
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_708])).

tff(c_5615,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_709])).

tff(c_5619,plain,(
    ! [E_182] :
      ( '#skF_2'('#skF_5','#skF_7',E_182,'#skF_10','#skF_8','#skF_6') = '#skF_9'
      | k1_xboole_0 = E_182 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5615,c_155])).

tff(c_194,plain,
    ( '#skF_2'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6') = '#skF_9'
    | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_136])).

tff(c_195,plain,(
    ! [E_182] :
      ( '#skF_2'('#skF_5','#skF_7',E_182,'#skF_10','#skF_8','#skF_6') = '#skF_9'
      | E_182 = '#skF_8'
      | '#skF_2'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6') = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_155])).

tff(c_5785,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_5859,plain,
    ( k4_mcart_1('#skF_1'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'),'#skF_9','#skF_3'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6')) = '#skF_10'
    | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_8'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5785,c_16])).

tff(c_5895,plain,
    ( k4_mcart_1('#skF_1'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'),'#skF_9','#skF_3'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5615,c_5859])).

tff(c_5896,plain,(
    k4_mcart_1('#skF_1'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'),'#skF_9','#skF_3'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_5895])).

tff(c_5910,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k9_mcart_1(A_9,B_10,C_11,D_12,k4_mcart_1('#skF_1'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'),'#skF_9','#skF_3'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6'))) = '#skF_9'
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_9,B_10,C_11,D_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5896,c_10])).

tff(c_6104,plain,(
    ! [A_2976,B_2977,C_2978,D_2979] :
      ( k9_mcart_1(A_2976,B_2977,C_2978,D_2979,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_2979
      | k1_xboole_0 = C_2978
      | k1_xboole_0 = B_2977
      | k1_xboole_0 = A_2976
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_2976,B_2977,C_2978,D_2979)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5910])).

tff(c_6107,plain,
    ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_6104])).

tff(c_6111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_26,c_6107])).

tff(c_6113,plain,(
    '#skF_2'('#skF_5','#skF_7','#skF_8','#skF_10','#skF_8','#skF_6') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_6147,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_5619,c_6113])).

tff(c_6155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_6147])).

tff(c_6157,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_709])).

tff(c_6158,plain,(
    ! [E_182] :
      ( k1_xboole_0 != E_182
      | '#skF_2'('#skF_5','#skF_7',E_182,'#skF_10','#skF_8','#skF_6') = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_6157])).

tff(c_20650,plain,(
    ! [E_56102] :
      ( k1_xboole_0 != E_56102
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_56102 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20628,c_6158])).

tff(c_20761,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20650])).

tff(c_20773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20761,c_6157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.12/4.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.06  
% 11.12/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.06  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 11.12/4.06  
% 11.12/4.06  %Foreground sorts:
% 11.12/4.06  
% 11.12/4.06  
% 11.12/4.06  %Background operators:
% 11.12/4.06  
% 11.12/4.06  
% 11.12/4.06  %Foreground operators:
% 11.12/4.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.12/4.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 11.12/4.06  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 11.12/4.06  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.12/4.06  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 11.12/4.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.12/4.06  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 11.12/4.06  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 11.12/4.06  tff('#skF_7', type, '#skF_7': $i).
% 11.12/4.06  tff('#skF_10', type, '#skF_10': $i).
% 11.12/4.06  tff('#skF_5', type, '#skF_5': $i).
% 11.12/4.06  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 11.12/4.06  tff('#skF_6', type, '#skF_6': $i).
% 11.12/4.06  tff('#skF_9', type, '#skF_9': $i).
% 11.12/4.06  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 11.12/4.06  tff('#skF_8', type, '#skF_8': $i).
% 11.12/4.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 11.12/4.06  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 11.12/4.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.12/4.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.12/4.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.12/4.06  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 11.12/4.06  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 11.12/4.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 11.12/4.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.12/4.06  
% 11.38/4.09  tff(f_113, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 11.38/4.09  tff(f_84, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 11.38/4.09  tff(f_56, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 11.38/4.09  tff(c_26, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.38/4.09  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.38/4.09  tff(c_32, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.38/4.09  tff(c_30, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.38/4.09  tff(c_28, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.38/4.09  tff(c_38, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.38/4.09  tff(c_16, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k4_mcart_1('#skF_1'(A_22, C_24, E_26, F_27, D_25, B_23), '#skF_2'(A_22, C_24, E_26, F_27, D_25, B_23), '#skF_3'(A_22, C_24, E_26, F_27, D_25, B_23), '#skF_4'(A_22, C_24, E_26, F_27, D_25, B_23))=F_27 | k8_mcart_1(A_22, B_23, C_24, D_25, F_27)=E_26 | k1_xboole_0=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(F_27, k4_zfmisc_1(A_22, B_23, C_24, D_25)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.38/4.09  tff(c_76, plain, (![D_162, C_159, B_163, A_158, F_161, E_160]: (k4_mcart_1('#skF_1'(A_158, C_159, E_160, F_161, D_162, B_163), '#skF_2'(A_158, C_159, E_160, F_161, D_162, B_163), '#skF_3'(A_158, C_159, E_160, F_161, D_162, B_163), '#skF_4'(A_158, C_159, E_160, F_161, D_162, B_163))=F_161 | k8_mcart_1(A_158, B_163, C_159, D_162, F_161)=E_160 | k1_xboole_0=D_162 | k1_xboole_0=C_159 | k1_xboole_0=B_163 | k1_xboole_0=A_158 | ~m1_subset_1(F_161, k4_zfmisc_1(A_158, B_163, C_159, D_162)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.38/4.09  tff(c_10, plain, (![H_20, C_11, F_18, I_21, B_10, G_19, D_12, A_9]: (k9_mcart_1(A_9, B_10, C_11, D_12, k4_mcart_1(F_18, G_19, H_20, I_21))=G_19 | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9 | ~m1_subset_1(k4_mcart_1(F_18, G_19, H_20, I_21), k4_zfmisc_1(A_9, B_10, C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.38/4.09  tff(c_528, plain, (![D_1878, D_1874, B_1870, A_1879, F_1871, C_1876, B_1875, A_1873, C_1877, E_1872]: (k9_mcart_1(A_1879, B_1875, C_1877, D_1878, k4_mcart_1('#skF_1'(A_1873, C_1876, E_1872, F_1871, D_1874, B_1870), '#skF_2'(A_1873, C_1876, E_1872, F_1871, D_1874, B_1870), '#skF_3'(A_1873, C_1876, E_1872, F_1871, D_1874, B_1870), '#skF_4'(A_1873, C_1876, E_1872, F_1871, D_1874, B_1870)))='#skF_2'(A_1873, C_1876, E_1872, F_1871, D_1874, B_1870) | k1_xboole_0=D_1878 | k1_xboole_0=C_1877 | k1_xboole_0=B_1875 | k1_xboole_0=A_1879 | ~m1_subset_1(F_1871, k4_zfmisc_1(A_1879, B_1875, C_1877, D_1878)) | k8_mcart_1(A_1873, B_1870, C_1876, D_1874, F_1871)=E_1872 | k1_xboole_0=D_1874 | k1_xboole_0=C_1876 | k1_xboole_0=B_1870 | k1_xboole_0=A_1873 | ~m1_subset_1(F_1871, k4_zfmisc_1(A_1873, B_1870, C_1876, D_1874)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_10])).
% 11.38/4.09  tff(c_20439, plain, (![A_55902, B_55906, C_55903, D_55909, E_55904, A_55901, B_55910, F_55905, C_55907, D_55908]: (k9_mcart_1(A_55902, B_55906, C_55907, D_55909, F_55905)='#skF_2'(A_55901, C_55903, E_55904, F_55905, D_55908, B_55910) | k1_xboole_0=D_55909 | k1_xboole_0=C_55907 | k1_xboole_0=B_55906 | k1_xboole_0=A_55902 | ~m1_subset_1(F_55905, k4_zfmisc_1(A_55902, B_55906, C_55907, D_55909)) | k8_mcart_1(A_55901, B_55910, C_55903, D_55908, F_55905)=E_55904 | k1_xboole_0=D_55908 | k1_xboole_0=C_55903 | k1_xboole_0=B_55910 | k1_xboole_0=A_55901 | ~m1_subset_1(F_55905, k4_zfmisc_1(A_55901, B_55910, C_55903, D_55908)) | k8_mcart_1(A_55901, B_55910, C_55903, D_55908, F_55905)=E_55904 | k1_xboole_0=D_55908 | k1_xboole_0=C_55903 | k1_xboole_0=B_55910 | k1_xboole_0=A_55901 | ~m1_subset_1(F_55905, k4_zfmisc_1(A_55901, B_55910, C_55903, D_55908)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_528])).
% 11.38/4.09  tff(c_20494, plain, (![C_55903, E_55904, A_55901, B_55910, D_55908]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_2'(A_55901, C_55903, E_55904, '#skF_10', D_55908, B_55910) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k8_mcart_1(A_55901, B_55910, C_55903, D_55908, '#skF_10')=E_55904 | k1_xboole_0=D_55908 | k1_xboole_0=C_55903 | k1_xboole_0=B_55910 | k1_xboole_0=A_55901 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_55901, B_55910, C_55903, D_55908)))), inference(resolution, [status(thm)], [c_38, c_20439])).
% 11.38/4.09  tff(c_20599, plain, (![C_56035, E_56038, D_56037, B_56036, A_56039]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_2'(A_56039, C_56035, E_56038, '#skF_10', D_56037, B_56036) | k8_mcart_1(A_56039, B_56036, C_56035, D_56037, '#skF_10')=E_56038 | k1_xboole_0=D_56037 | k1_xboole_0=C_56035 | k1_xboole_0=B_56036 | k1_xboole_0=A_56039 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_56039, B_56036, C_56035, D_56037)))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_20494])).
% 11.38/4.09  tff(c_20622, plain, (![E_56038]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_2'('#skF_5', '#skF_7', E_56038, '#skF_10', '#skF_8', '#skF_6') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_56038 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_38, c_20599])).
% 11.38/4.09  tff(c_20628, plain, (![E_56102]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_2'('#skF_5', '#skF_7', E_56102, '#skF_10', '#skF_8', '#skF_6') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_56102)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_20622])).
% 11.38/4.09  tff(c_18, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_4'(A_22, C_24, E_26, F_27, D_25, B_23), D_25) | k8_mcart_1(A_22, B_23, C_24, D_25, F_27)=E_26 | k1_xboole_0=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(F_27, k4_zfmisc_1(A_22, B_23, C_24, D_25)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.38/4.09  tff(c_20, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_3'(A_22, C_24, E_26, F_27, D_25, B_23), C_24) | k8_mcart_1(A_22, B_23, C_24, D_25, F_27)=E_26 | k1_xboole_0=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(F_27, k4_zfmisc_1(A_22, B_23, C_24, D_25)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.38/4.09  tff(c_24, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_1'(A_22, C_24, E_26, F_27, D_25, B_23), A_22) | k8_mcart_1(A_22, B_23, C_24, D_25, F_27)=E_26 | k1_xboole_0=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(F_27, k4_zfmisc_1(A_22, B_23, C_24, D_25)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.38/4.09  tff(c_22, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_2'(A_22, C_24, E_26, F_27, D_25, B_23), B_23) | k8_mcart_1(A_22, B_23, C_24, D_25, F_27)=E_26 | k1_xboole_0=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(F_27, k4_zfmisc_1(A_22, B_23, C_24, D_25)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.38/4.09  tff(c_36, plain, (![H_77, G_69, I_81, J_83]: (H_77='#skF_9' | k4_mcart_1(G_69, H_77, I_81, J_83)!='#skF_10' | ~m1_subset_1(J_83, '#skF_8') | ~m1_subset_1(I_81, '#skF_7') | ~m1_subset_1(H_77, '#skF_6') | ~m1_subset_1(G_69, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.38/4.09  tff(c_100, plain, (![C_169, E_166, A_167, D_168, B_164, F_165]: ('#skF_2'(A_167, C_169, E_166, F_165, D_168, B_164)='#skF_9' | F_165!='#skF_10' | ~m1_subset_1('#skF_4'(A_167, C_169, E_166, F_165, D_168, B_164), '#skF_8') | ~m1_subset_1('#skF_3'(A_167, C_169, E_166, F_165, D_168, B_164), '#skF_7') | ~m1_subset_1('#skF_2'(A_167, C_169, E_166, F_165, D_168, B_164), '#skF_6') | ~m1_subset_1('#skF_1'(A_167, C_169, E_166, F_165, D_168, B_164), '#skF_5') | k8_mcart_1(A_167, B_164, C_169, D_168, F_165)=E_166 | k1_xboole_0=D_168 | k1_xboole_0=C_169 | k1_xboole_0=B_164 | k1_xboole_0=A_167 | ~m1_subset_1(F_165, k4_zfmisc_1(A_167, B_164, C_169, D_168)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_36])).
% 11.38/4.09  tff(c_104, plain, (![E_26, F_27, A_22, D_25, C_24]: ('#skF_2'(A_22, C_24, E_26, F_27, D_25, '#skF_6')='#skF_9' | F_27!='#skF_10' | ~m1_subset_1('#skF_4'(A_22, C_24, E_26, F_27, D_25, '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_3'(A_22, C_24, E_26, F_27, D_25, '#skF_6'), '#skF_7') | ~m1_subset_1('#skF_1'(A_22, C_24, E_26, F_27, D_25, '#skF_6'), '#skF_5') | k8_mcart_1(A_22, '#skF_6', C_24, D_25, F_27)=E_26 | k1_xboole_0=D_25 | k1_xboole_0=C_24 | k1_xboole_0='#skF_6' | k1_xboole_0=A_22 | ~m1_subset_1(F_27, k4_zfmisc_1(A_22, '#skF_6', C_24, D_25)))), inference(resolution, [status(thm)], [c_22, c_100])).
% 11.38/4.09  tff(c_109, plain, (![C_171, A_170, F_173, D_174, E_172]: ('#skF_2'(A_170, C_171, E_172, F_173, D_174, '#skF_6')='#skF_9' | F_173!='#skF_10' | ~m1_subset_1('#skF_4'(A_170, C_171, E_172, F_173, D_174, '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_3'(A_170, C_171, E_172, F_173, D_174, '#skF_6'), '#skF_7') | ~m1_subset_1('#skF_1'(A_170, C_171, E_172, F_173, D_174, '#skF_6'), '#skF_5') | k8_mcart_1(A_170, '#skF_6', C_171, D_174, F_173)=E_172 | k1_xboole_0=D_174 | k1_xboole_0=C_171 | k1_xboole_0=A_170 | ~m1_subset_1(F_173, k4_zfmisc_1(A_170, '#skF_6', C_171, D_174)))), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_104])).
% 11.38/4.09  tff(c_113, plain, (![C_24, E_26, F_27, D_25]: ('#skF_2'('#skF_5', C_24, E_26, F_27, D_25, '#skF_6')='#skF_9' | F_27!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_5', C_24, E_26, F_27, D_25, '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_5', C_24, E_26, F_27, D_25, '#skF_6'), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_24, D_25, F_27)=E_26 | k1_xboole_0=D_25 | k1_xboole_0=C_24 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_27, k4_zfmisc_1('#skF_5', '#skF_6', C_24, D_25)))), inference(resolution, [status(thm)], [c_24, c_109])).
% 11.38/4.09  tff(c_118, plain, (![C_175, E_176, F_177, D_178]: ('#skF_2'('#skF_5', C_175, E_176, F_177, D_178, '#skF_6')='#skF_9' | F_177!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_5', C_175, E_176, F_177, D_178, '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_3'('#skF_5', C_175, E_176, F_177, D_178, '#skF_6'), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_175, D_178, F_177)=E_176 | k1_xboole_0=D_178 | k1_xboole_0=C_175 | ~m1_subset_1(F_177, k4_zfmisc_1('#skF_5', '#skF_6', C_175, D_178)))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_34, c_113])).
% 11.38/4.09  tff(c_122, plain, (![E_26, F_27, D_25]: ('#skF_2'('#skF_5', '#skF_7', E_26, F_27, D_25, '#skF_6')='#skF_9' | F_27!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_7', E_26, F_27, D_25, '#skF_6'), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_25, F_27)=E_26 | k1_xboole_0=D_25 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_27, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_25)))), inference(resolution, [status(thm)], [c_20, c_118])).
% 11.38/4.09  tff(c_127, plain, (![E_179, F_180, D_181]: ('#skF_2'('#skF_5', '#skF_7', E_179, F_180, D_181, '#skF_6')='#skF_9' | F_180!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_7', E_179, F_180, D_181, '#skF_6'), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_181, F_180)=E_179 | k1_xboole_0=D_181 | ~m1_subset_1(F_180, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_181)))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_30, c_122])).
% 11.38/4.09  tff(c_131, plain, (![E_26, F_27]: ('#skF_2'('#skF_5', '#skF_7', E_26, F_27, '#skF_8', '#skF_6')='#skF_9' | F_27!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_27)=E_26 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_27, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_18, c_127])).
% 11.38/4.09  tff(c_136, plain, (![E_182, F_183]: ('#skF_2'('#skF_5', '#skF_7', E_182, F_183, '#skF_8', '#skF_6')='#skF_9' | F_183!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_183)=E_182 | ~m1_subset_1(F_183, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_28, c_131])).
% 11.38/4.09  tff(c_155, plain, (![E_182]: ('#skF_2'('#skF_5', '#skF_7', E_182, '#skF_10', '#skF_8', '#skF_6')='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_182)), inference(resolution, [status(thm)], [c_38, c_136])).
% 11.38/4.09  tff(c_198, plain, ('#skF_2'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6')='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_136])).
% 11.38/4.09  tff(c_199, plain, (![E_182]: ('#skF_2'('#skF_5', '#skF_7', E_182, '#skF_10', '#skF_8', '#skF_6')='#skF_9' | k1_xboole_0=E_182 | '#skF_2'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6')='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_198, c_155])).
% 11.38/4.09  tff(c_689, plain, ('#skF_2'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6')='#skF_9'), inference(splitLeft, [status(thm)], [c_199])).
% 11.38/4.09  tff(c_82, plain, (![D_162, C_159, C_11, B_163, B_10, A_158, F_161, D_12, E_160, A_9]: (k9_mcart_1(A_9, B_10, C_11, D_12, k4_mcart_1('#skF_1'(A_158, C_159, E_160, F_161, D_162, B_163), '#skF_2'(A_158, C_159, E_160, F_161, D_162, B_163), '#skF_3'(A_158, C_159, E_160, F_161, D_162, B_163), '#skF_4'(A_158, C_159, E_160, F_161, D_162, B_163)))='#skF_2'(A_158, C_159, E_160, F_161, D_162, B_163) | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9 | ~m1_subset_1(F_161, k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k8_mcart_1(A_158, B_163, C_159, D_162, F_161)=E_160 | k1_xboole_0=D_162 | k1_xboole_0=C_159 | k1_xboole_0=B_163 | k1_xboole_0=A_158 | ~m1_subset_1(F_161, k4_zfmisc_1(A_158, B_163, C_159, D_162)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_10])).
% 11.38/4.09  tff(c_693, plain, (![A_9, B_10, C_11, D_12]: (k9_mcart_1(A_9, B_10, C_11, D_12, k4_mcart_1('#skF_1'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6'), '#skF_9', '#skF_3'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6')))='#skF_2'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6') | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_689, c_82])).
% 11.38/4.09  tff(c_708, plain, (![A_9, B_10, C_11, D_12]: (k9_mcart_1(A_9, B_10, C_11, D_12, k4_mcart_1('#skF_1'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6'), '#skF_9', '#skF_3'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6')))='#skF_9' | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_689, c_693])).
% 11.38/4.09  tff(c_709, plain, (![A_9, B_10, C_11, D_12]: (k9_mcart_1(A_9, B_10, C_11, D_12, k4_mcart_1('#skF_1'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6'), '#skF_9', '#skF_3'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', k1_xboole_0, '#skF_10', '#skF_8', '#skF_6')))='#skF_9' | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_708])).
% 11.38/4.09  tff(c_5615, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_709])).
% 11.38/4.09  tff(c_5619, plain, (![E_182]: ('#skF_2'('#skF_5', '#skF_7', E_182, '#skF_10', '#skF_8', '#skF_6')='#skF_9' | k1_xboole_0=E_182)), inference(demodulation, [status(thm), theory('equality')], [c_5615, c_155])).
% 11.38/4.09  tff(c_194, plain, ('#skF_2'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6')='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_8'), inference(resolution, [status(thm)], [c_38, c_136])).
% 11.38/4.09  tff(c_195, plain, (![E_182]: ('#skF_2'('#skF_5', '#skF_7', E_182, '#skF_10', '#skF_8', '#skF_6')='#skF_9' | E_182='#skF_8' | '#skF_2'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6')='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_194, c_155])).
% 11.38/4.09  tff(c_5785, plain, ('#skF_2'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6')='#skF_9'), inference(splitLeft, [status(thm)], [c_195])).
% 11.38/4.09  tff(c_5859, plain, (k4_mcart_1('#skF_1'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'), '#skF_9', '#skF_3'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_8' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5785, c_16])).
% 11.38/4.09  tff(c_5895, plain, (k4_mcart_1('#skF_1'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'), '#skF_9', '#skF_3'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5615, c_5859])).
% 11.38/4.09  tff(c_5896, plain, (k4_mcart_1('#skF_1'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'), '#skF_9', '#skF_3'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_5895])).
% 11.38/4.09  tff(c_5910, plain, (![A_9, B_10, C_11, D_12]: (k9_mcart_1(A_9, B_10, C_11, D_12, k4_mcart_1('#skF_1'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'), '#skF_9', '#skF_3'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6')))='#skF_9' | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_9, B_10, C_11, D_12)))), inference(superposition, [status(thm), theory('equality')], [c_5896, c_10])).
% 11.38/4.09  tff(c_6104, plain, (![A_2976, B_2977, C_2978, D_2979]: (k9_mcart_1(A_2976, B_2977, C_2978, D_2979, '#skF_10')='#skF_9' | k1_xboole_0=D_2979 | k1_xboole_0=C_2978 | k1_xboole_0=B_2977 | k1_xboole_0=A_2976 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_2976, B_2977, C_2978, D_2979)))), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5910])).
% 11.38/4.09  tff(c_6107, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_6104])).
% 11.38/4.09  tff(c_6111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_26, c_6107])).
% 11.38/4.09  tff(c_6113, plain, ('#skF_2'('#skF_5', '#skF_7', '#skF_8', '#skF_10', '#skF_8', '#skF_6')!='#skF_9'), inference(splitRight, [status(thm)], [c_195])).
% 11.38/4.09  tff(c_6147, plain, (k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_5619, c_6113])).
% 11.38/4.09  tff(c_6155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_6147])).
% 11.38/4.09  tff(c_6157, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_709])).
% 11.38/4.09  tff(c_6158, plain, (![E_182]: (k1_xboole_0!=E_182 | '#skF_2'('#skF_5', '#skF_7', E_182, '#skF_10', '#skF_8', '#skF_6')='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_155, c_6157])).
% 11.38/4.09  tff(c_20650, plain, (![E_56102]: (k1_xboole_0!=E_56102 | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_56102)), inference(superposition, [status(thm), theory('equality')], [c_20628, c_6158])).
% 11.38/4.09  tff(c_20761, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_20650])).
% 11.38/4.09  tff(c_20773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20761, c_6157])).
% 11.38/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/4.09  
% 11.38/4.09  Inference rules
% 11.38/4.09  ----------------------
% 11.38/4.09  #Ref     : 0
% 11.38/4.09  #Sup     : 4066
% 11.38/4.09  #Fact    : 20
% 11.38/4.09  #Define  : 0
% 11.38/4.09  #Split   : 50
% 11.38/4.09  #Chain   : 0
% 11.38/4.09  #Close   : 0
% 11.38/4.09  
% 11.38/4.09  Ordering : KBO
% 11.38/4.09  
% 11.38/4.09  Simplification rules
% 11.38/4.09  ----------------------
% 11.38/4.09  #Subsume      : 462
% 11.38/4.09  #Demod        : 3267
% 11.38/4.09  #Tautology    : 1539
% 11.38/4.09  #SimpNegUnit  : 1316
% 11.38/4.09  #BackRed      : 386
% 11.38/4.09  
% 11.38/4.09  #Partial instantiations: 2705
% 11.38/4.09  #Strategies tried      : 1
% 11.38/4.09  
% 11.38/4.09  Timing (in seconds)
% 11.38/4.09  ----------------------
% 11.38/4.09  Preprocessing        : 0.34
% 11.38/4.09  Parsing              : 0.18
% 11.38/4.09  CNF conversion       : 0.03
% 11.38/4.09  Main loop            : 2.96
% 11.38/4.09  Inferencing          : 1.21
% 11.38/4.09  Reduction            : 0.83
% 11.38/4.09  Demodulation         : 0.55
% 11.38/4.09  BG Simplification    : 0.13
% 11.38/4.09  Subsumption          : 0.61
% 11.38/4.09  Abstraction          : 0.23
% 11.38/4.09  MUC search           : 0.00
% 11.38/4.09  Cooper               : 0.00
% 11.38/4.09  Total                : 3.34
% 11.38/4.09  Index Insertion      : 0.00
% 11.38/4.09  Index Deletion       : 0.00
% 11.38/4.09  Index Matching       : 0.00
% 11.38/4.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
