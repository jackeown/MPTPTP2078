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
% DateTime   : Thu Dec  3 10:17:40 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 263 expanded)
%              Number of leaves         :   34 ( 109 expanded)
%              Depth                    :   23
%              Number of atoms          :  267 ( 869 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k6_funct_2,type,(
    k6_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_funct_2,type,(
    k7_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                   => r1_tarski(k5_setfam_1(A,D),k5_setfam_1(A,k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(A))
                     => ( m1_setfam_1(D,E)
                       => m1_setfam_1(k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A))) )
     => m1_subset_1(k7_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B))) )
     => m1_subset_1(k6_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_59,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_67,plain,(
    r1_tarski('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_110,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_4'(A_91,B_92),A_91)
      | r1_tarski(k3_tarski(A_91),B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_340,plain,(
    ! [A_139,B_140,B_141] :
      ( r2_hidden('#skF_4'(A_139,B_140),B_141)
      | ~ r1_tarski(A_139,B_141)
      | r1_tarski(k3_tarski(A_139),B_140) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_387,plain,(
    ! [A_157,B_158,A_159] :
      ( r1_tarski('#skF_4'(A_157,B_158),A_159)
      | ~ r1_tarski(A_157,k1_zfmisc_1(A_159))
      | r1_tarski(k3_tarski(A_157),B_158) ) ),
    inference(resolution,[status(thm)],[c_340,c_8])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( ~ r1_tarski('#skF_4'(A_11,B_12),B_12)
      | r1_tarski(k3_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_412,plain,(
    ! [A_157,A_159] :
      ( ~ r1_tarski(A_157,k1_zfmisc_1(A_159))
      | r1_tarski(k3_tarski(A_157),A_159) ) ),
    inference(resolution,[status(thm)],[c_387,c_20])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(A_84,B_85),A_84)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_86] : r1_tarski(A_86,A_86) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( m1_setfam_1(B_15,A_14)
      | ~ r1_tarski(A_14,k3_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_101,plain,(
    ! [B_15] : m1_setfam_1(B_15,k3_tarski(B_15)) ),
    inference(resolution,[status(thm)],[c_96,c_26])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_697,plain,(
    ! [D_196,A_193,C_194,E_192,B_195] :
      ( m1_setfam_1(k6_funct_2(A_193,B_195,C_194,k7_funct_2(A_193,B_195,C_194,D_196)),E_192)
      | ~ m1_setfam_1(D_196,E_192)
      | ~ m1_subset_1(E_192,k1_zfmisc_1(A_193))
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k1_zfmisc_1(A_193)))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_193,B_195)))
      | ~ v1_funct_2(C_194,A_193,B_195)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(B_195)
      | v1_xboole_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2939,plain,(
    ! [C_338,B_341,E_342,A_339,A_340] :
      ( m1_setfam_1(k6_funct_2(A_340,B_341,C_338,k7_funct_2(A_340,B_341,C_338,A_339)),E_342)
      | ~ m1_setfam_1(A_339,E_342)
      | ~ m1_subset_1(E_342,k1_zfmisc_1(A_340))
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341)))
      | ~ v1_funct_2(C_338,A_340,B_341)
      | ~ v1_funct_1(C_338)
      | v1_xboole_0(B_341)
      | v1_xboole_0(A_340)
      | ~ r1_tarski(A_339,k1_zfmisc_1(A_340)) ) ),
    inference(resolution,[status(thm)],[c_32,c_697])).

tff(c_2944,plain,(
    ! [A_339,E_342] :
      ( m1_setfam_1(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7',A_339)),E_342)
      | ~ m1_setfam_1(A_339,E_342)
      | ~ m1_subset_1(E_342,k1_zfmisc_1('#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0('#skF_5')
      | ~ r1_tarski(A_339,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2939])).

tff(c_2948,plain,(
    ! [A_339,E_342] :
      ( m1_setfam_1(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7',A_339)),E_342)
      | ~ m1_setfam_1(A_339,E_342)
      | ~ m1_subset_1(E_342,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0('#skF_5')
      | ~ r1_tarski(A_339,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2944])).

tff(c_2949,plain,(
    ! [A_339,E_342] :
      ( m1_setfam_1(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7',A_339)),E_342)
      | ~ m1_setfam_1(A_339,E_342)
      | ~ m1_subset_1(E_342,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski(A_339,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_2948])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ m1_setfam_1(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( m1_subset_1(k7_funct_2(A_24,B_25,C_26,D_27),k1_zfmisc_1(k1_zfmisc_1(B_25)))
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k1_zfmisc_1(A_24)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_624,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( m1_subset_1(k6_funct_2(A_179,B_180,C_181,D_182),k1_zfmisc_1(k1_zfmisc_1(A_179)))
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k1_zfmisc_1(B_180)))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(C_181,A_179,B_180)
      | ~ v1_funct_1(C_181)
      | v1_xboole_0(B_180)
      | v1_xboole_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2059,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( r1_tarski(k6_funct_2(A_297,B_298,C_299,D_300),k1_zfmisc_1(A_297))
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k1_zfmisc_1(B_298)))
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ v1_funct_2(C_299,A_297,B_298)
      | ~ v1_funct_1(C_299)
      | v1_xboole_0(B_298)
      | v1_xboole_0(A_297) ) ),
    inference(resolution,[status(thm)],[c_624,c_30])).

tff(c_706,plain,(
    ! [B_195,C_194,E_192] :
      ( m1_setfam_1(k6_funct_2('#skF_5',B_195,C_194,k7_funct_2('#skF_5',B_195,C_194,'#skF_8')),E_192)
      | ~ m1_setfam_1('#skF_8',E_192)
      | ~ m1_subset_1(E_192,k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_195)))
      | ~ v1_funct_2(C_194,'#skF_5',B_195)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(B_195)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_697])).

tff(c_849,plain,(
    ! [B_215,C_216,E_217] :
      ( m1_setfam_1(k6_funct_2('#skF_5',B_215,C_216,k7_funct_2('#skF_5',B_215,C_216,'#skF_8')),E_217)
      | ~ m1_setfam_1('#skF_8',E_217)
      | ~ m1_subset_1(E_217,k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_215)))
      | ~ v1_funct_2(C_216,'#skF_5',B_215)
      | ~ v1_funct_1(C_216)
      | v1_xboole_0(B_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_706])).

tff(c_854,plain,(
    ! [E_217] :
      ( m1_setfam_1(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')),E_217)
      | ~ m1_setfam_1('#skF_8',E_217)
      | ~ m1_subset_1(E_217,k1_zfmisc_1('#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_849])).

tff(c_858,plain,(
    ! [E_217] :
      ( m1_setfam_1(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')),E_217)
      | ~ m1_setfam_1('#skF_8',E_217)
      | ~ m1_subset_1(E_217,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_854])).

tff(c_1032,plain,(
    ! [E_233] :
      ( m1_setfam_1(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')),E_233)
      | ~ m1_setfam_1('#skF_8',E_233)
      | ~ m1_subset_1(E_233,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_858])).

tff(c_425,plain,(
    ! [A_164,A_165] :
      ( ~ r1_tarski(A_164,k1_zfmisc_1(A_165))
      | r1_tarski(k3_tarski(A_164),A_165) ) ),
    inference(resolution,[status(thm)],[c_387,c_20])).

tff(c_94,plain,(
    ! [A_84] : r1_tarski(A_84,A_84) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [C_88,B_89,A_90] :
      ( r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_176,plain,(
    ! [C_104,B_105,A_106] :
      ( r2_hidden(C_104,B_105)
      | ~ r1_tarski(k1_zfmisc_1(A_106),B_105)
      | ~ r1_tarski(C_104,A_106) ) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_252,plain,(
    ! [C_120,B_121,A_122] :
      ( r2_hidden(C_120,k3_tarski(B_121))
      | ~ r1_tarski(C_120,A_122)
      | ~ m1_setfam_1(B_121,k1_zfmisc_1(A_122)) ) ),
    inference(resolution,[status(thm)],[c_24,c_176])).

tff(c_277,plain,(
    ! [A_123,B_124] :
      ( r2_hidden(A_123,k3_tarski(B_124))
      | ~ m1_setfam_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(resolution,[status(thm)],[c_94,c_252])).

tff(c_284,plain,(
    ! [A_123,B_2,B_124] :
      ( r2_hidden(A_123,B_2)
      | ~ r1_tarski(k3_tarski(B_124),B_2)
      | ~ m1_setfam_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(resolution,[status(thm)],[c_277,c_2])).

tff(c_441,plain,(
    ! [A_123,A_165,A_164] :
      ( r2_hidden(A_123,A_165)
      | ~ m1_setfam_1(A_164,k1_zfmisc_1(A_123))
      | ~ r1_tarski(A_164,k1_zfmisc_1(A_165)) ) ),
    inference(resolution,[status(thm)],[c_425,c_284])).

tff(c_1069,plain,(
    ! [A_123,A_165] :
      ( r2_hidden(A_123,A_165)
      | ~ r1_tarski(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')),k1_zfmisc_1(A_165))
      | ~ m1_setfam_1('#skF_8',k1_zfmisc_1(A_123))
      | ~ m1_subset_1(k1_zfmisc_1(A_123),k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1032,c_441])).

tff(c_2064,plain,(
    ! [A_123] :
      ( r2_hidden(A_123,'#skF_5')
      | ~ m1_setfam_1('#skF_8',k1_zfmisc_1(A_123))
      | ~ m1_subset_1(k1_zfmisc_1(A_123),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2059,c_1069])).

tff(c_2106,plain,(
    ! [A_123] :
      ( r2_hidden(A_123,'#skF_5')
      | ~ m1_setfam_1('#skF_8',k1_zfmisc_1(A_123))
      | ~ m1_subset_1(k1_zfmisc_1(A_123),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2064])).

tff(c_2107,plain,(
    ! [A_123] :
      ( r2_hidden(A_123,'#skF_5')
      | ~ m1_setfam_1('#skF_8',k1_zfmisc_1(A_123))
      | ~ m1_subset_1(k1_zfmisc_1(A_123),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_2106])).

tff(c_2194,plain,(
    ~ m1_subset_1(k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_2107])).

tff(c_2197,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1('#skF_5')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2194])).

tff(c_2203,plain,
    ( v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_2197])).

tff(c_2205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_2203])).

tff(c_2207,plain,(
    m1_subset_1(k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_2107])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( k5_setfam_1(A_16,B_17) = k3_tarski(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2578,plain,(
    ! [A_326,B_327,C_328,D_329] :
      ( k5_setfam_1(A_326,k6_funct_2(A_326,B_327,C_328,D_329)) = k3_tarski(k6_funct_2(A_326,B_327,C_328,D_329))
      | ~ m1_subset_1(D_329,k1_zfmisc_1(k1_zfmisc_1(B_327)))
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_2(C_328,A_326,B_327)
      | ~ v1_funct_1(C_328)
      | v1_xboole_0(B_327)
      | v1_xboole_0(A_326) ) ),
    inference(resolution,[status(thm)],[c_624,c_28])).

tff(c_2580,plain,(
    ! [A_326,C_328] :
      ( k5_setfam_1(A_326,k6_funct_2(A_326,'#skF_6',C_328,k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'))) = k3_tarski(k6_funct_2(A_326,'#skF_6',C_328,k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')))
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,'#skF_6')))
      | ~ v1_funct_2(C_328,A_326,'#skF_6')
      | ~ v1_funct_1(C_328)
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_326) ) ),
    inference(resolution,[status(thm)],[c_2207,c_2578])).

tff(c_3371,plain,(
    ! [A_385,C_386] :
      ( k5_setfam_1(A_385,k6_funct_2(A_385,'#skF_6',C_386,k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'))) = k3_tarski(k6_funct_2(A_385,'#skF_6',C_386,k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')))
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_385,'#skF_6')))
      | ~ v1_funct_2(C_386,A_385,'#skF_6')
      | ~ v1_funct_1(C_386)
      | v1_xboole_0(A_385) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2580])).

tff(c_3376,plain,
    ( k5_setfam_1('#skF_5',k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'))) = k3_tarski(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_3371])).

tff(c_3380,plain,
    ( k5_setfam_1('#skF_5',k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'))) = k3_tarski(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3376])).

tff(c_3381,plain,(
    k5_setfam_1('#skF_5',k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'))) = k3_tarski(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3380])).

tff(c_124,plain,(
    ! [A_95,B_96] :
      ( k5_setfam_1(A_95,B_96) = k3_tarski(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k1_zfmisc_1(A_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_133,plain,(
    k5_setfam_1('#skF_5','#skF_8') = k3_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_124])).

tff(c_40,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_5','#skF_8'),k5_setfam_1('#skF_5',k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_134,plain,(
    ~ r1_tarski(k3_tarski('#skF_8'),k5_setfam_1('#skF_5',k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_40])).

tff(c_3666,plain,(
    ~ r1_tarski(k3_tarski('#skF_8'),k3_tarski(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3381,c_134])).

tff(c_4424,plain,(
    ~ m1_setfam_1(k6_funct_2('#skF_5','#skF_6','#skF_7',k7_funct_2('#skF_5','#skF_6','#skF_7','#skF_8')),k3_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_24,c_3666])).

tff(c_4427,plain,
    ( ~ m1_setfam_1('#skF_8',k3_tarski('#skF_8'))
    | ~ m1_subset_1(k3_tarski('#skF_8'),k1_zfmisc_1('#skF_5'))
    | ~ r1_tarski('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2949,c_4424])).

tff(c_4433,plain,(
    ~ m1_subset_1(k3_tarski('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_101,c_4427])).

tff(c_4440,plain,(
    ~ r1_tarski(k3_tarski('#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_4433])).

tff(c_4446,plain,(
    ~ r1_tarski('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_412,c_4440])).

tff(c_4456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_4446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:07:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.07/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/2.48  
% 7.07/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/2.48  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 7.07/2.48  
% 7.07/2.48  %Foreground sorts:
% 7.07/2.48  
% 7.07/2.48  
% 7.07/2.48  %Background operators:
% 7.07/2.48  
% 7.07/2.48  
% 7.07/2.48  %Foreground operators:
% 7.07/2.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.07/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.07/2.48  tff(k6_funct_2, type, k6_funct_2: ($i * $i * $i * $i) > $i).
% 7.07/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.07/2.48  tff('#skF_7', type, '#skF_7': $i).
% 7.07/2.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.07/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.07/2.48  tff('#skF_5', type, '#skF_5': $i).
% 7.07/2.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.07/2.48  tff('#skF_6', type, '#skF_6': $i).
% 7.07/2.48  tff(k7_funct_2, type, k7_funct_2: ($i * $i * $i * $i) > $i).
% 7.07/2.48  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 7.07/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.07/2.48  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.07/2.48  tff('#skF_8', type, '#skF_8': $i).
% 7.07/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.07/2.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.07/2.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.07/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.07/2.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.07/2.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.07/2.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.07/2.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.07/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.07/2.48  
% 7.36/2.52  tff(f_134, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => r1_tarski(k5_setfam_1(A, D), k5_setfam_1(A, k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_funct_2)).
% 7.36/2.52  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.36/2.52  tff(f_46, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 7.36/2.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.36/2.52  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.36/2.52  tff(f_50, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 7.36/2.52  tff(f_114, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (m1_setfam_1(D, E) => m1_setfam_1(k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_funct_2)).
% 7.36/2.52  tff(f_90, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A)))) => m1_subset_1(k7_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 7.36/2.52  tff(f_74, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B)))) => m1_subset_1(k6_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 7.36/2.52  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 7.36/2.52  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.36/2.52  tff(c_59, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.36/2.52  tff(c_67, plain, (r1_tarski('#skF_8', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_59])).
% 7.36/2.52  tff(c_110, plain, (![A_91, B_92]: (r2_hidden('#skF_4'(A_91, B_92), A_91) | r1_tarski(k3_tarski(A_91), B_92))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.36/2.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.36/2.52  tff(c_340, plain, (![A_139, B_140, B_141]: (r2_hidden('#skF_4'(A_139, B_140), B_141) | ~r1_tarski(A_139, B_141) | r1_tarski(k3_tarski(A_139), B_140))), inference(resolution, [status(thm)], [c_110, c_2])).
% 7.36/2.52  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.36/2.52  tff(c_387, plain, (![A_157, B_158, A_159]: (r1_tarski('#skF_4'(A_157, B_158), A_159) | ~r1_tarski(A_157, k1_zfmisc_1(A_159)) | r1_tarski(k3_tarski(A_157), B_158))), inference(resolution, [status(thm)], [c_340, c_8])).
% 7.36/2.52  tff(c_20, plain, (![A_11, B_12]: (~r1_tarski('#skF_4'(A_11, B_12), B_12) | r1_tarski(k3_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.36/2.52  tff(c_412, plain, (![A_157, A_159]: (~r1_tarski(A_157, k1_zfmisc_1(A_159)) | r1_tarski(k3_tarski(A_157), A_159))), inference(resolution, [status(thm)], [c_387, c_20])).
% 7.36/2.52  tff(c_32, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.36/2.52  tff(c_85, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(A_84, B_85), A_84) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.36/2.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.36/2.52  tff(c_96, plain, (![A_86]: (r1_tarski(A_86, A_86))), inference(resolution, [status(thm)], [c_85, c_4])).
% 7.36/2.52  tff(c_26, plain, (![B_15, A_14]: (m1_setfam_1(B_15, A_14) | ~r1_tarski(A_14, k3_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.36/2.52  tff(c_101, plain, (![B_15]: (m1_setfam_1(B_15, k3_tarski(B_15)))), inference(resolution, [status(thm)], [c_96, c_26])).
% 7.36/2.52  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.36/2.52  tff(c_50, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.36/2.52  tff(c_48, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.36/2.52  tff(c_46, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.36/2.52  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.36/2.52  tff(c_697, plain, (![D_196, A_193, C_194, E_192, B_195]: (m1_setfam_1(k6_funct_2(A_193, B_195, C_194, k7_funct_2(A_193, B_195, C_194, D_196)), E_192) | ~m1_setfam_1(D_196, E_192) | ~m1_subset_1(E_192, k1_zfmisc_1(A_193)) | ~m1_subset_1(D_196, k1_zfmisc_1(k1_zfmisc_1(A_193))) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_193, B_195))) | ~v1_funct_2(C_194, A_193, B_195) | ~v1_funct_1(C_194) | v1_xboole_0(B_195) | v1_xboole_0(A_193))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.36/2.52  tff(c_2939, plain, (![C_338, B_341, E_342, A_339, A_340]: (m1_setfam_1(k6_funct_2(A_340, B_341, C_338, k7_funct_2(A_340, B_341, C_338, A_339)), E_342) | ~m1_setfam_1(A_339, E_342) | ~m1_subset_1(E_342, k1_zfmisc_1(A_340)) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))) | ~v1_funct_2(C_338, A_340, B_341) | ~v1_funct_1(C_338) | v1_xboole_0(B_341) | v1_xboole_0(A_340) | ~r1_tarski(A_339, k1_zfmisc_1(A_340)))), inference(resolution, [status(thm)], [c_32, c_697])).
% 7.36/2.52  tff(c_2944, plain, (![A_339, E_342]: (m1_setfam_1(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', A_339)), E_342) | ~m1_setfam_1(A_339, E_342) | ~m1_subset_1(E_342, k1_zfmisc_1('#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5') | ~r1_tarski(A_339, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_44, c_2939])).
% 7.36/2.52  tff(c_2948, plain, (![A_339, E_342]: (m1_setfam_1(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', A_339)), E_342) | ~m1_setfam_1(A_339, E_342) | ~m1_subset_1(E_342, k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5') | ~r1_tarski(A_339, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2944])).
% 7.36/2.52  tff(c_2949, plain, (![A_339, E_342]: (m1_setfam_1(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', A_339)), E_342) | ~m1_setfam_1(A_339, E_342) | ~m1_subset_1(E_342, k1_zfmisc_1('#skF_5')) | ~r1_tarski(A_339, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_2948])).
% 7.36/2.52  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~m1_setfam_1(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.36/2.52  tff(c_36, plain, (![A_24, B_25, C_26, D_27]: (m1_subset_1(k7_funct_2(A_24, B_25, C_26, D_27), k1_zfmisc_1(k1_zfmisc_1(B_25))) | ~m1_subset_1(D_27, k1_zfmisc_1(k1_zfmisc_1(A_24))) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26) | v1_xboole_0(B_25) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.52  tff(c_624, plain, (![A_179, B_180, C_181, D_182]: (m1_subset_1(k6_funct_2(A_179, B_180, C_181, D_182), k1_zfmisc_1(k1_zfmisc_1(A_179))) | ~m1_subset_1(D_182, k1_zfmisc_1(k1_zfmisc_1(B_180))) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(C_181, A_179, B_180) | ~v1_funct_1(C_181) | v1_xboole_0(B_180) | v1_xboole_0(A_179))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.36/2.52  tff(c_30, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.36/2.52  tff(c_2059, plain, (![A_297, B_298, C_299, D_300]: (r1_tarski(k6_funct_2(A_297, B_298, C_299, D_300), k1_zfmisc_1(A_297)) | ~m1_subset_1(D_300, k1_zfmisc_1(k1_zfmisc_1(B_298))) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~v1_funct_2(C_299, A_297, B_298) | ~v1_funct_1(C_299) | v1_xboole_0(B_298) | v1_xboole_0(A_297))), inference(resolution, [status(thm)], [c_624, c_30])).
% 7.36/2.52  tff(c_706, plain, (![B_195, C_194, E_192]: (m1_setfam_1(k6_funct_2('#skF_5', B_195, C_194, k7_funct_2('#skF_5', B_195, C_194, '#skF_8')), E_192) | ~m1_setfam_1('#skF_8', E_192) | ~m1_subset_1(E_192, k1_zfmisc_1('#skF_5')) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_195))) | ~v1_funct_2(C_194, '#skF_5', B_195) | ~v1_funct_1(C_194) | v1_xboole_0(B_195) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_697])).
% 7.36/2.52  tff(c_849, plain, (![B_215, C_216, E_217]: (m1_setfam_1(k6_funct_2('#skF_5', B_215, C_216, k7_funct_2('#skF_5', B_215, C_216, '#skF_8')), E_217) | ~m1_setfam_1('#skF_8', E_217) | ~m1_subset_1(E_217, k1_zfmisc_1('#skF_5')) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_215))) | ~v1_funct_2(C_216, '#skF_5', B_215) | ~v1_funct_1(C_216) | v1_xboole_0(B_215))), inference(negUnitSimplification, [status(thm)], [c_52, c_706])).
% 7.36/2.52  tff(c_854, plain, (![E_217]: (m1_setfam_1(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')), E_217) | ~m1_setfam_1('#skF_8', E_217) | ~m1_subset_1(E_217, k1_zfmisc_1('#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_849])).
% 7.36/2.52  tff(c_858, plain, (![E_217]: (m1_setfam_1(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')), E_217) | ~m1_setfam_1('#skF_8', E_217) | ~m1_subset_1(E_217, k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_854])).
% 7.36/2.52  tff(c_1032, plain, (![E_233]: (m1_setfam_1(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')), E_233) | ~m1_setfam_1('#skF_8', E_233) | ~m1_subset_1(E_233, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_50, c_858])).
% 7.36/2.52  tff(c_425, plain, (![A_164, A_165]: (~r1_tarski(A_164, k1_zfmisc_1(A_165)) | r1_tarski(k3_tarski(A_164), A_165))), inference(resolution, [status(thm)], [c_387, c_20])).
% 7.36/2.52  tff(c_94, plain, (![A_84]: (r1_tarski(A_84, A_84))), inference(resolution, [status(thm)], [c_85, c_4])).
% 7.36/2.52  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.36/2.52  tff(c_103, plain, (![C_88, B_89, A_90]: (r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.36/2.52  tff(c_176, plain, (![C_104, B_105, A_106]: (r2_hidden(C_104, B_105) | ~r1_tarski(k1_zfmisc_1(A_106), B_105) | ~r1_tarski(C_104, A_106))), inference(resolution, [status(thm)], [c_10, c_103])).
% 7.36/2.52  tff(c_252, plain, (![C_120, B_121, A_122]: (r2_hidden(C_120, k3_tarski(B_121)) | ~r1_tarski(C_120, A_122) | ~m1_setfam_1(B_121, k1_zfmisc_1(A_122)))), inference(resolution, [status(thm)], [c_24, c_176])).
% 7.36/2.52  tff(c_277, plain, (![A_123, B_124]: (r2_hidden(A_123, k3_tarski(B_124)) | ~m1_setfam_1(B_124, k1_zfmisc_1(A_123)))), inference(resolution, [status(thm)], [c_94, c_252])).
% 7.36/2.52  tff(c_284, plain, (![A_123, B_2, B_124]: (r2_hidden(A_123, B_2) | ~r1_tarski(k3_tarski(B_124), B_2) | ~m1_setfam_1(B_124, k1_zfmisc_1(A_123)))), inference(resolution, [status(thm)], [c_277, c_2])).
% 7.36/2.52  tff(c_441, plain, (![A_123, A_165, A_164]: (r2_hidden(A_123, A_165) | ~m1_setfam_1(A_164, k1_zfmisc_1(A_123)) | ~r1_tarski(A_164, k1_zfmisc_1(A_165)))), inference(resolution, [status(thm)], [c_425, c_284])).
% 7.36/2.52  tff(c_1069, plain, (![A_123, A_165]: (r2_hidden(A_123, A_165) | ~r1_tarski(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')), k1_zfmisc_1(A_165)) | ~m1_setfam_1('#skF_8', k1_zfmisc_1(A_123)) | ~m1_subset_1(k1_zfmisc_1(A_123), k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1032, c_441])).
% 7.36/2.52  tff(c_2064, plain, (![A_123]: (r2_hidden(A_123, '#skF_5') | ~m1_setfam_1('#skF_8', k1_zfmisc_1(A_123)) | ~m1_subset_1(k1_zfmisc_1(A_123), k1_zfmisc_1('#skF_5')) | ~m1_subset_1(k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_2059, c_1069])).
% 7.36/2.52  tff(c_2106, plain, (![A_123]: (r2_hidden(A_123, '#skF_5') | ~m1_setfam_1('#skF_8', k1_zfmisc_1(A_123)) | ~m1_subset_1(k1_zfmisc_1(A_123), k1_zfmisc_1('#skF_5')) | ~m1_subset_1(k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2064])).
% 7.36/2.52  tff(c_2107, plain, (![A_123]: (r2_hidden(A_123, '#skF_5') | ~m1_setfam_1('#skF_8', k1_zfmisc_1(A_123)) | ~m1_subset_1(k1_zfmisc_1(A_123), k1_zfmisc_1('#skF_5')) | ~m1_subset_1(k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_2106])).
% 7.36/2.52  tff(c_2194, plain, (~m1_subset_1(k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_2107])).
% 7.36/2.52  tff(c_2197, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2194])).
% 7.36/2.52  tff(c_2203, plain, (v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_2197])).
% 7.36/2.52  tff(c_2205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_2203])).
% 7.36/2.52  tff(c_2207, plain, (m1_subset_1(k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_2107])).
% 7.36/2.52  tff(c_28, plain, (![A_16, B_17]: (k5_setfam_1(A_16, B_17)=k3_tarski(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.36/2.52  tff(c_2578, plain, (![A_326, B_327, C_328, D_329]: (k5_setfam_1(A_326, k6_funct_2(A_326, B_327, C_328, D_329))=k3_tarski(k6_funct_2(A_326, B_327, C_328, D_329)) | ~m1_subset_1(D_329, k1_zfmisc_1(k1_zfmisc_1(B_327))) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_2(C_328, A_326, B_327) | ~v1_funct_1(C_328) | v1_xboole_0(B_327) | v1_xboole_0(A_326))), inference(resolution, [status(thm)], [c_624, c_28])).
% 7.36/2.52  tff(c_2580, plain, (![A_326, C_328]: (k5_setfam_1(A_326, k6_funct_2(A_326, '#skF_6', C_328, k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')))=k3_tarski(k6_funct_2(A_326, '#skF_6', C_328, k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'))) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, '#skF_6'))) | ~v1_funct_2(C_328, A_326, '#skF_6') | ~v1_funct_1(C_328) | v1_xboole_0('#skF_6') | v1_xboole_0(A_326))), inference(resolution, [status(thm)], [c_2207, c_2578])).
% 7.36/2.52  tff(c_3371, plain, (![A_385, C_386]: (k5_setfam_1(A_385, k6_funct_2(A_385, '#skF_6', C_386, k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')))=k3_tarski(k6_funct_2(A_385, '#skF_6', C_386, k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'))) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_385, '#skF_6'))) | ~v1_funct_2(C_386, A_385, '#skF_6') | ~v1_funct_1(C_386) | v1_xboole_0(A_385))), inference(negUnitSimplification, [status(thm)], [c_50, c_2580])).
% 7.36/2.52  tff(c_3376, plain, (k5_setfam_1('#skF_5', k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')))=k3_tarski(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_3371])).
% 7.36/2.52  tff(c_3380, plain, (k5_setfam_1('#skF_5', k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')))=k3_tarski(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3376])).
% 7.36/2.52  tff(c_3381, plain, (k5_setfam_1('#skF_5', k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')))=k3_tarski(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_52, c_3380])).
% 7.36/2.52  tff(c_124, plain, (![A_95, B_96]: (k5_setfam_1(A_95, B_96)=k3_tarski(B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(k1_zfmisc_1(A_95))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.36/2.52  tff(c_133, plain, (k5_setfam_1('#skF_5', '#skF_8')=k3_tarski('#skF_8')), inference(resolution, [status(thm)], [c_42, c_124])).
% 7.36/2.52  tff(c_40, plain, (~r1_tarski(k5_setfam_1('#skF_5', '#skF_8'), k5_setfam_1('#skF_5', k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.36/2.52  tff(c_134, plain, (~r1_tarski(k3_tarski('#skF_8'), k5_setfam_1('#skF_5', k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_40])).
% 7.36/2.52  tff(c_3666, plain, (~r1_tarski(k3_tarski('#skF_8'), k3_tarski(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_3381, c_134])).
% 7.36/2.52  tff(c_4424, plain, (~m1_setfam_1(k6_funct_2('#skF_5', '#skF_6', '#skF_7', k7_funct_2('#skF_5', '#skF_6', '#skF_7', '#skF_8')), k3_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_24, c_3666])).
% 7.36/2.52  tff(c_4427, plain, (~m1_setfam_1('#skF_8', k3_tarski('#skF_8')) | ~m1_subset_1(k3_tarski('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_8', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_2949, c_4424])).
% 7.36/2.52  tff(c_4433, plain, (~m1_subset_1(k3_tarski('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_101, c_4427])).
% 7.36/2.52  tff(c_4440, plain, (~r1_tarski(k3_tarski('#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_32, c_4433])).
% 7.36/2.52  tff(c_4446, plain, (~r1_tarski('#skF_8', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_412, c_4440])).
% 7.36/2.52  tff(c_4456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_4446])).
% 7.36/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.52  
% 7.36/2.52  Inference rules
% 7.36/2.52  ----------------------
% 7.36/2.52  #Ref     : 0
% 7.36/2.52  #Sup     : 1044
% 7.36/2.52  #Fact    : 0
% 7.36/2.52  #Define  : 0
% 7.36/2.52  #Split   : 14
% 7.36/2.52  #Chain   : 0
% 7.36/2.52  #Close   : 0
% 7.36/2.52  
% 7.36/2.52  Ordering : KBO
% 7.36/2.52  
% 7.36/2.52  Simplification rules
% 7.36/2.52  ----------------------
% 7.36/2.52  #Subsume      : 51
% 7.36/2.52  #Demod        : 41
% 7.36/2.52  #Tautology    : 47
% 7.36/2.52  #SimpNegUnit  : 12
% 7.36/2.52  #BackRed      : 3
% 7.36/2.52  
% 7.36/2.52  #Partial instantiations: 0
% 7.36/2.52  #Strategies tried      : 1
% 7.36/2.52  
% 7.36/2.52  Timing (in seconds)
% 7.36/2.52  ----------------------
% 7.36/2.53  Preprocessing        : 0.35
% 7.36/2.53  Parsing              : 0.19
% 7.36/2.53  CNF conversion       : 0.03
% 7.36/2.53  Main loop            : 1.34
% 7.36/2.53  Inferencing          : 0.42
% 7.36/2.53  Reduction            : 0.37
% 7.36/2.53  Demodulation         : 0.25
% 7.36/2.53  BG Simplification    : 0.05
% 7.36/2.53  Subsumption          : 0.39
% 7.36/2.53  Abstraction          : 0.07
% 7.36/2.53  MUC search           : 0.00
% 7.36/2.53  Cooper               : 0.00
% 7.36/2.53  Total                : 1.76
% 7.36/2.53  Index Insertion      : 0.00
% 7.36/2.53  Index Deletion       : 0.00
% 7.36/2.53  Index Matching       : 0.00
% 7.36/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
