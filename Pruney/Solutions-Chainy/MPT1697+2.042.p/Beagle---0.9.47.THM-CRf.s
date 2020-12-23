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
% DateTime   : Thu Dec  3 10:26:15 EST 2020

% Result     : Theorem 14.97s
% Output     : CNFRefutation 15.01s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 743 expanded)
%              Number of leaves         :   44 ( 281 expanded)
%              Depth                    :   14
%              Number of atoms          :  648 (2908 expanded)
%              Number of equality atoms :  140 ( 704 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_229,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(A)) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ( r1_subset_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_187,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_153,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_2976,plain,(
    ! [C_465,A_466,B_467] :
      ( v1_relat_1(C_465)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(k2_zfmisc_1(A_466,B_467))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2984,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_2976])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    ! [A_229,B_230] :
      ( k4_xboole_0(A_229,B_230) = A_229
      | ~ r1_xboole_0(A_229,B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_92,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(resolution,[status(thm)],[c_16,c_84])).

tff(c_3040,plain,(
    ! [A_476,B_477] : k4_xboole_0(A_476,k4_xboole_0(A_476,B_477)) = k3_xboole_0(A_476,B_477) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3066,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_3040])).

tff(c_3070,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3066])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3071,plain,(
    ! [A_478] : k4_xboole_0(A_478,A_478) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3066])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3076,plain,(
    ! [A_478] : k4_xboole_0(A_478,k1_xboole_0) = k3_xboole_0(A_478,A_478) ),
    inference(superposition,[status(thm),theory(equality)],[c_3071,c_14])).

tff(c_3100,plain,(
    ! [A_479] : k3_xboole_0(A_479,A_479) = A_479 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3076])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_17809,plain,(
    ! [A_1119,C_1120] :
      ( ~ r1_xboole_0(A_1119,A_1119)
      | ~ r2_hidden(C_1120,A_1119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3100,c_10])).

tff(c_17815,plain,(
    ! [C_1120,B_16] :
      ( ~ r2_hidden(C_1120,B_16)
      | k4_xboole_0(B_16,B_16) != B_16 ) ),
    inference(resolution,[status(thm)],[c_20,c_17809])).

tff(c_17824,plain,(
    ! [C_1121,B_1122] :
      ( ~ r2_hidden(C_1121,B_1122)
      | k1_xboole_0 != B_1122 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3070,c_17815])).

tff(c_17832,plain,(
    ! [A_1,B_2] :
      ( k1_xboole_0 != A_1
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_17824])).

tff(c_18317,plain,(
    ! [A_1166,B_1167] :
      ( k7_relat_1(A_1166,B_1167) = k1_xboole_0
      | ~ r1_xboole_0(B_1167,k1_relat_1(A_1166))
      | ~ v1_relat_1(A_1166) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18349,plain,(
    ! [A_1168,A_1169] :
      ( k7_relat_1(A_1168,A_1169) = k1_xboole_0
      | ~ v1_relat_1(A_1168)
      | k1_xboole_0 != A_1169 ) ),
    inference(resolution,[status(thm)],[c_17832,c_18317])).

tff(c_18356,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2984,c_18349])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_2983,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_2976])).

tff(c_18366,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2983,c_18349])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_62,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_17899,plain,(
    ! [A_1129,B_1130] :
      ( r1_xboole_0(A_1129,B_1130)
      | ~ r1_subset_1(A_1129,B_1130)
      | v1_xboole_0(B_1130)
      | v1_xboole_0(A_1129) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20167,plain,(
    ! [A_1305,B_1306] :
      ( k4_xboole_0(A_1305,B_1306) = A_1305
      | ~ r1_subset_1(A_1305,B_1306)
      | v1_xboole_0(B_1306)
      | v1_xboole_0(A_1305) ) ),
    inference(resolution,[status(thm)],[c_17899,c_18])).

tff(c_20176,plain,
    ( k4_xboole_0('#skF_5','#skF_6') = '#skF_5'
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_20167])).

tff(c_20181,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_20176])).

tff(c_20223,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_20181,c_14])).

tff(c_20246,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3070,c_20223])).

tff(c_18470,plain,(
    ! [A_1177,B_1178,C_1179] :
      ( k9_subset_1(A_1177,B_1178,C_1179) = k3_xboole_0(B_1178,C_1179)
      | ~ m1_subset_1(C_1179,k1_zfmisc_1(A_1177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18482,plain,(
    ! [B_1178] : k9_subset_1('#skF_3',B_1178,'#skF_6') = k3_xboole_0(B_1178,'#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_18470])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_58,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_54,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_52,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_18838,plain,(
    ! [C_1207,D_1204,B_1202,F_1203,A_1205,E_1206] :
      ( v1_funct_1(k1_tmap_1(A_1205,B_1202,C_1207,D_1204,E_1206,F_1203))
      | ~ m1_subset_1(F_1203,k1_zfmisc_1(k2_zfmisc_1(D_1204,B_1202)))
      | ~ v1_funct_2(F_1203,D_1204,B_1202)
      | ~ v1_funct_1(F_1203)
      | ~ m1_subset_1(E_1206,k1_zfmisc_1(k2_zfmisc_1(C_1207,B_1202)))
      | ~ v1_funct_2(E_1206,C_1207,B_1202)
      | ~ v1_funct_1(E_1206)
      | ~ m1_subset_1(D_1204,k1_zfmisc_1(A_1205))
      | v1_xboole_0(D_1204)
      | ~ m1_subset_1(C_1207,k1_zfmisc_1(A_1205))
      | v1_xboole_0(C_1207)
      | v1_xboole_0(B_1202)
      | v1_xboole_0(A_1205) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_18842,plain,(
    ! [A_1205,C_1207,E_1206] :
      ( v1_funct_1(k1_tmap_1(A_1205,'#skF_4',C_1207,'#skF_6',E_1206,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1206,k1_zfmisc_1(k2_zfmisc_1(C_1207,'#skF_4')))
      | ~ v1_funct_2(E_1206,C_1207,'#skF_4')
      | ~ v1_funct_1(E_1206)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1205))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1207,k1_zfmisc_1(A_1205))
      | v1_xboole_0(C_1207)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1205) ) ),
    inference(resolution,[status(thm)],[c_50,c_18838])).

tff(c_18849,plain,(
    ! [A_1205,C_1207,E_1206] :
      ( v1_funct_1(k1_tmap_1(A_1205,'#skF_4',C_1207,'#skF_6',E_1206,'#skF_8'))
      | ~ m1_subset_1(E_1206,k1_zfmisc_1(k2_zfmisc_1(C_1207,'#skF_4')))
      | ~ v1_funct_2(E_1206,C_1207,'#skF_4')
      | ~ v1_funct_1(E_1206)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1205))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1207,k1_zfmisc_1(A_1205))
      | v1_xboole_0(C_1207)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_18842])).

tff(c_19571,plain,(
    ! [A_1266,C_1267,E_1268] :
      ( v1_funct_1(k1_tmap_1(A_1266,'#skF_4',C_1267,'#skF_6',E_1268,'#skF_8'))
      | ~ m1_subset_1(E_1268,k1_zfmisc_1(k2_zfmisc_1(C_1267,'#skF_4')))
      | ~ v1_funct_2(E_1268,C_1267,'#skF_4')
      | ~ v1_funct_1(E_1268)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1266))
      | ~ m1_subset_1(C_1267,k1_zfmisc_1(A_1266))
      | v1_xboole_0(C_1267)
      | v1_xboole_0(A_1266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_18849])).

tff(c_19576,plain,(
    ! [A_1266] :
      ( v1_funct_1(k1_tmap_1(A_1266,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1266))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1266))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1266) ) ),
    inference(resolution,[status(thm)],[c_56,c_19571])).

tff(c_19584,plain,(
    ! [A_1266] :
      ( v1_funct_1(k1_tmap_1(A_1266,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1266))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1266))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_19576])).

tff(c_20089,plain,(
    ! [A_1299] :
      ( v1_funct_1(k1_tmap_1(A_1299,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1299))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1299))
      | v1_xboole_0(A_1299) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_19584])).

tff(c_20092,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_20089])).

tff(c_20095,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20092])).

tff(c_20096,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_20095])).

tff(c_18687,plain,(
    ! [A_1193,B_1194,C_1195,D_1196] :
      ( k2_partfun1(A_1193,B_1194,C_1195,D_1196) = k7_relat_1(C_1195,D_1196)
      | ~ m1_subset_1(C_1195,k1_zfmisc_1(k2_zfmisc_1(A_1193,B_1194)))
      | ~ v1_funct_1(C_1195) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_18689,plain,(
    ! [D_1196] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_1196) = k7_relat_1('#skF_7',D_1196)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_56,c_18687])).

tff(c_18694,plain,(
    ! [D_1196] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_1196) = k7_relat_1('#skF_7',D_1196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_18689])).

tff(c_18691,plain,(
    ! [D_1196] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_1196) = k7_relat_1('#skF_8',D_1196)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_18687])).

tff(c_18697,plain,(
    ! [D_1196] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_1196) = k7_relat_1('#skF_8',D_1196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18691])).

tff(c_44,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( v1_funct_2(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k4_subset_1(A_162,C_164,D_165),B_163)
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_42,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( m1_subset_1(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162,C_164,D_165),B_163)))
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_19730,plain,(
    ! [B_1276,C_1278,D_1277,A_1274,F_1273,E_1275] :
      ( k2_partfun1(k4_subset_1(A_1274,C_1278,D_1277),B_1276,k1_tmap_1(A_1274,B_1276,C_1278,D_1277,E_1275,F_1273),C_1278) = E_1275
      | ~ m1_subset_1(k1_tmap_1(A_1274,B_1276,C_1278,D_1277,E_1275,F_1273),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1274,C_1278,D_1277),B_1276)))
      | ~ v1_funct_2(k1_tmap_1(A_1274,B_1276,C_1278,D_1277,E_1275,F_1273),k4_subset_1(A_1274,C_1278,D_1277),B_1276)
      | ~ v1_funct_1(k1_tmap_1(A_1274,B_1276,C_1278,D_1277,E_1275,F_1273))
      | k2_partfun1(D_1277,B_1276,F_1273,k9_subset_1(A_1274,C_1278,D_1277)) != k2_partfun1(C_1278,B_1276,E_1275,k9_subset_1(A_1274,C_1278,D_1277))
      | ~ m1_subset_1(F_1273,k1_zfmisc_1(k2_zfmisc_1(D_1277,B_1276)))
      | ~ v1_funct_2(F_1273,D_1277,B_1276)
      | ~ v1_funct_1(F_1273)
      | ~ m1_subset_1(E_1275,k1_zfmisc_1(k2_zfmisc_1(C_1278,B_1276)))
      | ~ v1_funct_2(E_1275,C_1278,B_1276)
      | ~ v1_funct_1(E_1275)
      | ~ m1_subset_1(D_1277,k1_zfmisc_1(A_1274))
      | v1_xboole_0(D_1277)
      | ~ m1_subset_1(C_1278,k1_zfmisc_1(A_1274))
      | v1_xboole_0(C_1278)
      | v1_xboole_0(B_1276)
      | v1_xboole_0(A_1274) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_34585,plain,(
    ! [B_1858,E_1862,D_1860,A_1861,C_1863,F_1859] :
      ( k2_partfun1(k4_subset_1(A_1861,C_1863,D_1860),B_1858,k1_tmap_1(A_1861,B_1858,C_1863,D_1860,E_1862,F_1859),C_1863) = E_1862
      | ~ v1_funct_2(k1_tmap_1(A_1861,B_1858,C_1863,D_1860,E_1862,F_1859),k4_subset_1(A_1861,C_1863,D_1860),B_1858)
      | ~ v1_funct_1(k1_tmap_1(A_1861,B_1858,C_1863,D_1860,E_1862,F_1859))
      | k2_partfun1(D_1860,B_1858,F_1859,k9_subset_1(A_1861,C_1863,D_1860)) != k2_partfun1(C_1863,B_1858,E_1862,k9_subset_1(A_1861,C_1863,D_1860))
      | ~ m1_subset_1(F_1859,k1_zfmisc_1(k2_zfmisc_1(D_1860,B_1858)))
      | ~ v1_funct_2(F_1859,D_1860,B_1858)
      | ~ v1_funct_1(F_1859)
      | ~ m1_subset_1(E_1862,k1_zfmisc_1(k2_zfmisc_1(C_1863,B_1858)))
      | ~ v1_funct_2(E_1862,C_1863,B_1858)
      | ~ v1_funct_1(E_1862)
      | ~ m1_subset_1(D_1860,k1_zfmisc_1(A_1861))
      | v1_xboole_0(D_1860)
      | ~ m1_subset_1(C_1863,k1_zfmisc_1(A_1861))
      | v1_xboole_0(C_1863)
      | v1_xboole_0(B_1858)
      | v1_xboole_0(A_1861) ) ),
    inference(resolution,[status(thm)],[c_42,c_19730])).

tff(c_40806,plain,(
    ! [A_2078,F_2076,C_2080,B_2075,E_2079,D_2077] :
      ( k2_partfun1(k4_subset_1(A_2078,C_2080,D_2077),B_2075,k1_tmap_1(A_2078,B_2075,C_2080,D_2077,E_2079,F_2076),C_2080) = E_2079
      | ~ v1_funct_1(k1_tmap_1(A_2078,B_2075,C_2080,D_2077,E_2079,F_2076))
      | k2_partfun1(D_2077,B_2075,F_2076,k9_subset_1(A_2078,C_2080,D_2077)) != k2_partfun1(C_2080,B_2075,E_2079,k9_subset_1(A_2078,C_2080,D_2077))
      | ~ m1_subset_1(F_2076,k1_zfmisc_1(k2_zfmisc_1(D_2077,B_2075)))
      | ~ v1_funct_2(F_2076,D_2077,B_2075)
      | ~ v1_funct_1(F_2076)
      | ~ m1_subset_1(E_2079,k1_zfmisc_1(k2_zfmisc_1(C_2080,B_2075)))
      | ~ v1_funct_2(E_2079,C_2080,B_2075)
      | ~ v1_funct_1(E_2079)
      | ~ m1_subset_1(D_2077,k1_zfmisc_1(A_2078))
      | v1_xboole_0(D_2077)
      | ~ m1_subset_1(C_2080,k1_zfmisc_1(A_2078))
      | v1_xboole_0(C_2080)
      | v1_xboole_0(B_2075)
      | v1_xboole_0(A_2078) ) ),
    inference(resolution,[status(thm)],[c_44,c_34585])).

tff(c_40812,plain,(
    ! [A_2078,C_2080,E_2079] :
      ( k2_partfun1(k4_subset_1(A_2078,C_2080,'#skF_6'),'#skF_4',k1_tmap_1(A_2078,'#skF_4',C_2080,'#skF_6',E_2079,'#skF_8'),C_2080) = E_2079
      | ~ v1_funct_1(k1_tmap_1(A_2078,'#skF_4',C_2080,'#skF_6',E_2079,'#skF_8'))
      | k2_partfun1(C_2080,'#skF_4',E_2079,k9_subset_1(A_2078,C_2080,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_2078,C_2080,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_2079,k1_zfmisc_1(k2_zfmisc_1(C_2080,'#skF_4')))
      | ~ v1_funct_2(E_2079,C_2080,'#skF_4')
      | ~ v1_funct_1(E_2079)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2078))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_2080,k1_zfmisc_1(A_2078))
      | v1_xboole_0(C_2080)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2078) ) ),
    inference(resolution,[status(thm)],[c_50,c_40806])).

tff(c_40820,plain,(
    ! [A_2078,C_2080,E_2079] :
      ( k2_partfun1(k4_subset_1(A_2078,C_2080,'#skF_6'),'#skF_4',k1_tmap_1(A_2078,'#skF_4',C_2080,'#skF_6',E_2079,'#skF_8'),C_2080) = E_2079
      | ~ v1_funct_1(k1_tmap_1(A_2078,'#skF_4',C_2080,'#skF_6',E_2079,'#skF_8'))
      | k2_partfun1(C_2080,'#skF_4',E_2079,k9_subset_1(A_2078,C_2080,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2078,C_2080,'#skF_6'))
      | ~ m1_subset_1(E_2079,k1_zfmisc_1(k2_zfmisc_1(C_2080,'#skF_4')))
      | ~ v1_funct_2(E_2079,C_2080,'#skF_4')
      | ~ v1_funct_1(E_2079)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2078))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_2080,k1_zfmisc_1(A_2078))
      | v1_xboole_0(C_2080)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2078) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_18697,c_40812])).

tff(c_47460,plain,(
    ! [A_2207,C_2208,E_2209] :
      ( k2_partfun1(k4_subset_1(A_2207,C_2208,'#skF_6'),'#skF_4',k1_tmap_1(A_2207,'#skF_4',C_2208,'#skF_6',E_2209,'#skF_8'),C_2208) = E_2209
      | ~ v1_funct_1(k1_tmap_1(A_2207,'#skF_4',C_2208,'#skF_6',E_2209,'#skF_8'))
      | k2_partfun1(C_2208,'#skF_4',E_2209,k9_subset_1(A_2207,C_2208,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2207,C_2208,'#skF_6'))
      | ~ m1_subset_1(E_2209,k1_zfmisc_1(k2_zfmisc_1(C_2208,'#skF_4')))
      | ~ v1_funct_2(E_2209,C_2208,'#skF_4')
      | ~ v1_funct_1(E_2209)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2207))
      | ~ m1_subset_1(C_2208,k1_zfmisc_1(A_2207))
      | v1_xboole_0(C_2208)
      | v1_xboole_0(A_2207) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_40820])).

tff(c_47465,plain,(
    ! [A_2207] :
      ( k2_partfun1(k4_subset_1(A_2207,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2207,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2207,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_2207,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2207,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2207))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2207))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2207) ) ),
    inference(resolution,[status(thm)],[c_56,c_47460])).

tff(c_47473,plain,(
    ! [A_2207] :
      ( k2_partfun1(k4_subset_1(A_2207,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2207,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2207,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2207,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2207,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2207))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2207))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_18694,c_47465])).

tff(c_48125,plain,(
    ! [A_2215] :
      ( k2_partfun1(k4_subset_1(A_2215,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2215,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2215,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2215,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2215,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2215))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2215))
      | v1_xboole_0(A_2215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_47473])).

tff(c_3165,plain,(
    ! [A_484,C_485] :
      ( ~ r1_xboole_0(A_484,A_484)
      | ~ r2_hidden(C_485,A_484) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3100,c_10])).

tff(c_3171,plain,(
    ! [C_485,B_16] :
      ( ~ r2_hidden(C_485,B_16)
      | k4_xboole_0(B_16,B_16) != B_16 ) ),
    inference(resolution,[status(thm)],[c_20,c_3165])).

tff(c_3180,plain,(
    ! [C_486,B_487] :
      ( ~ r2_hidden(C_486,B_487)
      | k1_xboole_0 != B_487 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3070,c_3171])).

tff(c_3188,plain,(
    ! [A_1,B_2] :
      ( k1_xboole_0 != A_1
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_3180])).

tff(c_3533,plain,(
    ! [A_520,B_521] :
      ( k7_relat_1(A_520,B_521) = k1_xboole_0
      | ~ r1_xboole_0(B_521,k1_relat_1(A_520))
      | ~ v1_relat_1(A_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3561,plain,(
    ! [A_524,A_525] :
      ( k7_relat_1(A_524,A_525) = k1_xboole_0
      | ~ v1_relat_1(A_524)
      | k1_xboole_0 != A_525 ) ),
    inference(resolution,[status(thm)],[c_3188,c_3533])).

tff(c_3568,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2984,c_3561])).

tff(c_3578,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2983,c_3561])).

tff(c_3255,plain,(
    ! [A_494,B_495] :
      ( r1_xboole_0(A_494,B_495)
      | ~ r1_subset_1(A_494,B_495)
      | v1_xboole_0(B_495)
      | v1_xboole_0(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5220,plain,(
    ! [A_657,B_658] :
      ( k4_xboole_0(A_657,B_658) = A_657
      | ~ r1_subset_1(A_657,B_658)
      | v1_xboole_0(B_658)
      | v1_xboole_0(A_657) ) ),
    inference(resolution,[status(thm)],[c_3255,c_18])).

tff(c_5229,plain,
    ( k4_xboole_0('#skF_5','#skF_6') = '#skF_5'
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_5220])).

tff(c_5234,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_5229])).

tff(c_5270,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5234,c_14])).

tff(c_5289,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3070,c_5270])).

tff(c_3710,plain,(
    ! [A_535,B_536,C_537] :
      ( k9_subset_1(A_535,B_536,C_537) = k3_xboole_0(B_536,C_537)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(A_535)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3722,plain,(
    ! [B_536] : k9_subset_1('#skF_3',B_536,'#skF_6') = k3_xboole_0(B_536,'#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_3710])).

tff(c_3896,plain,(
    ! [C_558,D_555,A_556,F_554,B_553,E_557] :
      ( v1_funct_1(k1_tmap_1(A_556,B_553,C_558,D_555,E_557,F_554))
      | ~ m1_subset_1(F_554,k1_zfmisc_1(k2_zfmisc_1(D_555,B_553)))
      | ~ v1_funct_2(F_554,D_555,B_553)
      | ~ v1_funct_1(F_554)
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(C_558,B_553)))
      | ~ v1_funct_2(E_557,C_558,B_553)
      | ~ v1_funct_1(E_557)
      | ~ m1_subset_1(D_555,k1_zfmisc_1(A_556))
      | v1_xboole_0(D_555)
      | ~ m1_subset_1(C_558,k1_zfmisc_1(A_556))
      | v1_xboole_0(C_558)
      | v1_xboole_0(B_553)
      | v1_xboole_0(A_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3900,plain,(
    ! [A_556,C_558,E_557] :
      ( v1_funct_1(k1_tmap_1(A_556,'#skF_4',C_558,'#skF_6',E_557,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(C_558,'#skF_4')))
      | ~ v1_funct_2(E_557,C_558,'#skF_4')
      | ~ v1_funct_1(E_557)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_556))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_558,k1_zfmisc_1(A_556))
      | v1_xboole_0(C_558)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_556) ) ),
    inference(resolution,[status(thm)],[c_50,c_3896])).

tff(c_3907,plain,(
    ! [A_556,C_558,E_557] :
      ( v1_funct_1(k1_tmap_1(A_556,'#skF_4',C_558,'#skF_6',E_557,'#skF_8'))
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(C_558,'#skF_4')))
      | ~ v1_funct_2(E_557,C_558,'#skF_4')
      | ~ v1_funct_1(E_557)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_556))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_558,k1_zfmisc_1(A_556))
      | v1_xboole_0(C_558)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_556) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3900])).

tff(c_3969,plain,(
    ! [A_563,C_564,E_565] :
      ( v1_funct_1(k1_tmap_1(A_563,'#skF_4',C_564,'#skF_6',E_565,'#skF_8'))
      | ~ m1_subset_1(E_565,k1_zfmisc_1(k2_zfmisc_1(C_564,'#skF_4')))
      | ~ v1_funct_2(E_565,C_564,'#skF_4')
      | ~ v1_funct_1(E_565)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_563))
      | ~ m1_subset_1(C_564,k1_zfmisc_1(A_563))
      | v1_xboole_0(C_564)
      | v1_xboole_0(A_563) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_3907])).

tff(c_3971,plain,(
    ! [A_563] :
      ( v1_funct_1(k1_tmap_1(A_563,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_563))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_563))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_563) ) ),
    inference(resolution,[status(thm)],[c_56,c_3969])).

tff(c_3976,plain,(
    ! [A_563] :
      ( v1_funct_1(k1_tmap_1(A_563,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_563))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_563))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_563) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3971])).

tff(c_4313,plain,(
    ! [A_601] :
      ( v1_funct_1(k1_tmap_1(A_601,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_601))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_601))
      | v1_xboole_0(A_601) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3976])).

tff(c_4316,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_4313])).

tff(c_4319,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4316])).

tff(c_4320,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4319])).

tff(c_3769,plain,(
    ! [A_543,B_544,C_545,D_546] :
      ( k2_partfun1(A_543,B_544,C_545,D_546) = k7_relat_1(C_545,D_546)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(A_543,B_544)))
      | ~ v1_funct_1(C_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3771,plain,(
    ! [D_546] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_546) = k7_relat_1('#skF_7',D_546)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_56,c_3769])).

tff(c_3776,plain,(
    ! [D_546] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_546) = k7_relat_1('#skF_7',D_546) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3771])).

tff(c_3773,plain,(
    ! [D_546] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_546) = k7_relat_1('#skF_8',D_546)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_3769])).

tff(c_3779,plain,(
    ! [D_546] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_546) = k7_relat_1('#skF_8',D_546) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3773])).

tff(c_4895,plain,(
    ! [E_631,C_634,D_633,A_630,B_632,F_629] :
      ( k2_partfun1(k4_subset_1(A_630,C_634,D_633),B_632,k1_tmap_1(A_630,B_632,C_634,D_633,E_631,F_629),D_633) = F_629
      | ~ m1_subset_1(k1_tmap_1(A_630,B_632,C_634,D_633,E_631,F_629),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_630,C_634,D_633),B_632)))
      | ~ v1_funct_2(k1_tmap_1(A_630,B_632,C_634,D_633,E_631,F_629),k4_subset_1(A_630,C_634,D_633),B_632)
      | ~ v1_funct_1(k1_tmap_1(A_630,B_632,C_634,D_633,E_631,F_629))
      | k2_partfun1(D_633,B_632,F_629,k9_subset_1(A_630,C_634,D_633)) != k2_partfun1(C_634,B_632,E_631,k9_subset_1(A_630,C_634,D_633))
      | ~ m1_subset_1(F_629,k1_zfmisc_1(k2_zfmisc_1(D_633,B_632)))
      | ~ v1_funct_2(F_629,D_633,B_632)
      | ~ v1_funct_1(F_629)
      | ~ m1_subset_1(E_631,k1_zfmisc_1(k2_zfmisc_1(C_634,B_632)))
      | ~ v1_funct_2(E_631,C_634,B_632)
      | ~ v1_funct_1(E_631)
      | ~ m1_subset_1(D_633,k1_zfmisc_1(A_630))
      | v1_xboole_0(D_633)
      | ~ m1_subset_1(C_634,k1_zfmisc_1(A_630))
      | v1_xboole_0(C_634)
      | v1_xboole_0(B_632)
      | v1_xboole_0(A_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_8156,plain,(
    ! [D_803,F_802,B_801,C_806,E_805,A_804] :
      ( k2_partfun1(k4_subset_1(A_804,C_806,D_803),B_801,k1_tmap_1(A_804,B_801,C_806,D_803,E_805,F_802),D_803) = F_802
      | ~ v1_funct_2(k1_tmap_1(A_804,B_801,C_806,D_803,E_805,F_802),k4_subset_1(A_804,C_806,D_803),B_801)
      | ~ v1_funct_1(k1_tmap_1(A_804,B_801,C_806,D_803,E_805,F_802))
      | k2_partfun1(D_803,B_801,F_802,k9_subset_1(A_804,C_806,D_803)) != k2_partfun1(C_806,B_801,E_805,k9_subset_1(A_804,C_806,D_803))
      | ~ m1_subset_1(F_802,k1_zfmisc_1(k2_zfmisc_1(D_803,B_801)))
      | ~ v1_funct_2(F_802,D_803,B_801)
      | ~ v1_funct_1(F_802)
      | ~ m1_subset_1(E_805,k1_zfmisc_1(k2_zfmisc_1(C_806,B_801)))
      | ~ v1_funct_2(E_805,C_806,B_801)
      | ~ v1_funct_1(E_805)
      | ~ m1_subset_1(D_803,k1_zfmisc_1(A_804))
      | v1_xboole_0(D_803)
      | ~ m1_subset_1(C_806,k1_zfmisc_1(A_804))
      | v1_xboole_0(C_806)
      | v1_xboole_0(B_801)
      | v1_xboole_0(A_804) ) ),
    inference(resolution,[status(thm)],[c_42,c_4895])).

tff(c_15351,plain,(
    ! [F_1039,E_1042,C_1043,D_1040,B_1038,A_1041] :
      ( k2_partfun1(k4_subset_1(A_1041,C_1043,D_1040),B_1038,k1_tmap_1(A_1041,B_1038,C_1043,D_1040,E_1042,F_1039),D_1040) = F_1039
      | ~ v1_funct_1(k1_tmap_1(A_1041,B_1038,C_1043,D_1040,E_1042,F_1039))
      | k2_partfun1(D_1040,B_1038,F_1039,k9_subset_1(A_1041,C_1043,D_1040)) != k2_partfun1(C_1043,B_1038,E_1042,k9_subset_1(A_1041,C_1043,D_1040))
      | ~ m1_subset_1(F_1039,k1_zfmisc_1(k2_zfmisc_1(D_1040,B_1038)))
      | ~ v1_funct_2(F_1039,D_1040,B_1038)
      | ~ v1_funct_1(F_1039)
      | ~ m1_subset_1(E_1042,k1_zfmisc_1(k2_zfmisc_1(C_1043,B_1038)))
      | ~ v1_funct_2(E_1042,C_1043,B_1038)
      | ~ v1_funct_1(E_1042)
      | ~ m1_subset_1(D_1040,k1_zfmisc_1(A_1041))
      | v1_xboole_0(D_1040)
      | ~ m1_subset_1(C_1043,k1_zfmisc_1(A_1041))
      | v1_xboole_0(C_1043)
      | v1_xboole_0(B_1038)
      | v1_xboole_0(A_1041) ) ),
    inference(resolution,[status(thm)],[c_44,c_8156])).

tff(c_15357,plain,(
    ! [A_1041,C_1043,E_1042] :
      ( k2_partfun1(k4_subset_1(A_1041,C_1043,'#skF_6'),'#skF_4',k1_tmap_1(A_1041,'#skF_4',C_1043,'#skF_6',E_1042,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1041,'#skF_4',C_1043,'#skF_6',E_1042,'#skF_8'))
      | k2_partfun1(C_1043,'#skF_4',E_1042,k9_subset_1(A_1041,C_1043,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_1041,C_1043,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1042,k1_zfmisc_1(k2_zfmisc_1(C_1043,'#skF_4')))
      | ~ v1_funct_2(E_1042,C_1043,'#skF_4')
      | ~ v1_funct_1(E_1042)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1041))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1043,k1_zfmisc_1(A_1041))
      | v1_xboole_0(C_1043)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1041) ) ),
    inference(resolution,[status(thm)],[c_50,c_15351])).

tff(c_15365,plain,(
    ! [A_1041,C_1043,E_1042] :
      ( k2_partfun1(k4_subset_1(A_1041,C_1043,'#skF_6'),'#skF_4',k1_tmap_1(A_1041,'#skF_4',C_1043,'#skF_6',E_1042,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1041,'#skF_4',C_1043,'#skF_6',E_1042,'#skF_8'))
      | k2_partfun1(C_1043,'#skF_4',E_1042,k9_subset_1(A_1041,C_1043,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1041,C_1043,'#skF_6'))
      | ~ m1_subset_1(E_1042,k1_zfmisc_1(k2_zfmisc_1(C_1043,'#skF_4')))
      | ~ v1_funct_2(E_1042,C_1043,'#skF_4')
      | ~ v1_funct_1(E_1042)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1041))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1043,k1_zfmisc_1(A_1041))
      | v1_xboole_0(C_1043)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1041) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3779,c_15357])).

tff(c_16686,plain,(
    ! [A_1097,C_1098,E_1099] :
      ( k2_partfun1(k4_subset_1(A_1097,C_1098,'#skF_6'),'#skF_4',k1_tmap_1(A_1097,'#skF_4',C_1098,'#skF_6',E_1099,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1097,'#skF_4',C_1098,'#skF_6',E_1099,'#skF_8'))
      | k2_partfun1(C_1098,'#skF_4',E_1099,k9_subset_1(A_1097,C_1098,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1097,C_1098,'#skF_6'))
      | ~ m1_subset_1(E_1099,k1_zfmisc_1(k2_zfmisc_1(C_1098,'#skF_4')))
      | ~ v1_funct_2(E_1099,C_1098,'#skF_4')
      | ~ v1_funct_1(E_1099)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1097))
      | ~ m1_subset_1(C_1098,k1_zfmisc_1(A_1097))
      | v1_xboole_0(C_1098)
      | v1_xboole_0(A_1097) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_15365])).

tff(c_16691,plain,(
    ! [A_1097] :
      ( k2_partfun1(k4_subset_1(A_1097,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1097,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1097,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_1097,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1097,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1097))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1097))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1097) ) ),
    inference(resolution,[status(thm)],[c_56,c_16686])).

tff(c_16699,plain,(
    ! [A_1097] :
      ( k2_partfun1(k4_subset_1(A_1097,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1097,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1097,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1097,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1097,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1097))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1097))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1097) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3776,c_16691])).

tff(c_17779,plain,(
    ! [A_1118] :
      ( k2_partfun1(k4_subset_1(A_1118,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1118,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1118,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1118,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1118,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1118))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1118))
      | v1_xboole_0(A_1118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_16699])).

tff(c_205,plain,(
    ! [C_246,A_247,B_248] :
      ( v1_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_213,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_205])).

tff(c_214,plain,(
    ! [A_249,B_250] :
      ( r2_hidden('#skF_1'(A_249,B_250),A_249)
      | r1_xboole_0(A_249,B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [A_234,B_235] : k4_xboole_0(A_234,k4_xboole_0(A_234,B_235)) = k3_xboole_0(A_234,B_235) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_139,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_124])).

tff(c_142,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_139])).

tff(c_150,plain,(
    ! [A_240] : k4_xboole_0(A_240,A_240) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_139])).

tff(c_155,plain,(
    ! [A_240] : k4_xboole_0(A_240,k1_xboole_0) = k3_xboole_0(A_240,A_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_14])).

tff(c_171,plain,(
    ! [A_241] : k3_xboole_0(A_241,A_241) = A_241 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_155])).

tff(c_193,plain,(
    ! [A_242,C_243] :
      ( ~ r1_xboole_0(A_242,A_242)
      | ~ r2_hidden(C_243,A_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_10])).

tff(c_196,plain,(
    ! [C_243,B_16] :
      ( ~ r2_hidden(C_243,B_16)
      | k4_xboole_0(B_16,B_16) != B_16 ) ),
    inference(resolution,[status(thm)],[c_20,c_193])).

tff(c_201,plain,(
    ! [C_243,B_16] :
      ( ~ r2_hidden(C_243,B_16)
      | k1_xboole_0 != B_16 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_196])).

tff(c_226,plain,(
    ! [A_249,B_250] :
      ( k1_xboole_0 != A_249
      | r1_xboole_0(A_249,B_250) ) ),
    inference(resolution,[status(thm)],[c_214,c_201])).

tff(c_459,plain,(
    ! [A_269,B_270] :
      ( k7_relat_1(A_269,B_270) = k1_xboole_0
      | ~ r1_xboole_0(B_270,k1_relat_1(A_269))
      | ~ v1_relat_1(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_798,plain,(
    ! [A_300,A_301] :
      ( k7_relat_1(A_300,A_301) = k1_xboole_0
      | ~ v1_relat_1(A_300)
      | k1_xboole_0 != A_301 ) ),
    inference(resolution,[status(thm)],[c_226,c_459])).

tff(c_834,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_213,c_798])).

tff(c_212,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_205])).

tff(c_844,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_212,c_798])).

tff(c_712,plain,(
    ! [A_290,B_291] :
      ( r1_xboole_0(A_290,B_291)
      | ~ r1_subset_1(A_290,B_291)
      | v1_xboole_0(B_291)
      | v1_xboole_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2873,plain,(
    ! [A_461,B_462] :
      ( k4_xboole_0(A_461,B_462) = A_461
      | ~ r1_subset_1(A_461,B_462)
      | v1_xboole_0(B_462)
      | v1_xboole_0(A_461) ) ),
    inference(resolution,[status(thm)],[c_712,c_18])).

tff(c_2885,plain,
    ( k4_xboole_0('#skF_5','#skF_6') = '#skF_5'
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2873])).

tff(c_2891,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_2885])).

tff(c_2939,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2891,c_14])).

tff(c_2964,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2939])).

tff(c_922,plain,(
    ! [A_315,B_316,C_317,D_318] :
      ( k2_partfun1(A_315,B_316,C_317,D_318) = k7_relat_1(C_317,D_318)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316)))
      | ~ v1_funct_1(C_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_926,plain,(
    ! [D_318] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_318) = k7_relat_1('#skF_8',D_318)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_922])).

tff(c_932,plain,(
    ! [D_318] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_318) = k7_relat_1('#skF_8',D_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_926])).

tff(c_924,plain,(
    ! [D_318] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_318) = k7_relat_1('#skF_7',D_318)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_56,c_922])).

tff(c_929,plain,(
    ! [D_318] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_318) = k7_relat_1('#skF_7',D_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_924])).

tff(c_872,plain,(
    ! [A_308,B_309,C_310] :
      ( k9_subset_1(A_308,B_309,C_310) = k3_xboole_0(B_309,C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(A_308)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_884,plain,(
    ! [B_309] : k9_subset_1('#skF_3',B_309,'#skF_6') = k3_xboole_0(B_309,'#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_872])).

tff(c_48,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_121,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_894,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_884,c_121])).

tff(c_1016,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k7_relat_1('#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_929,c_894])).

tff(c_2967,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) != k7_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2964,c_2964,c_1016])).

tff(c_2970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_844,c_2967])).

tff(c_2971,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3164,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2971])).

tff(c_17790,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17779,c_3164])).

tff(c_17804,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_3568,c_3578,c_5289,c_5289,c_3722,c_3722,c_4320,c_17790])).

tff(c_17806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_17804])).

tff(c_17807,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2971])).

tff(c_48137,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48125,c_17807])).

tff(c_48151,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_18356,c_18366,c_20246,c_18482,c_20246,c_18482,c_20096,c_48137])).

tff(c_48153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_48151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n009.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:54:26 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.97/7.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.01/7.61  
% 15.01/7.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.01/7.62  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 15.01/7.62  
% 15.01/7.62  %Foreground sorts:
% 15.01/7.62  
% 15.01/7.62  
% 15.01/7.62  %Background operators:
% 15.01/7.62  
% 15.01/7.62  
% 15.01/7.62  %Foreground operators:
% 15.01/7.62  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 15.01/7.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.01/7.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.01/7.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.01/7.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.01/7.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.01/7.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.01/7.62  tff('#skF_7', type, '#skF_7': $i).
% 15.01/7.62  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 15.01/7.62  tff('#skF_5', type, '#skF_5': $i).
% 15.01/7.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.01/7.62  tff('#skF_6', type, '#skF_6': $i).
% 15.01/7.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.01/7.62  tff('#skF_3', type, '#skF_3': $i).
% 15.01/7.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.01/7.62  tff('#skF_8', type, '#skF_8': $i).
% 15.01/7.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.01/7.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.01/7.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.01/7.62  tff('#skF_4', type, '#skF_4': $i).
% 15.01/7.62  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.01/7.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.01/7.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.01/7.62  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.01/7.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.01/7.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.01/7.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.01/7.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.01/7.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.01/7.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.01/7.62  
% 15.01/7.65  tff(f_229, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 15.01/7.65  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.01/7.65  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 15.01/7.65  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 15.01/7.65  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 15.01/7.65  tff(f_67, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.01/7.65  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.01/7.65  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 15.01/7.65  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 15.01/7.65  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 15.01/7.65  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 15.01/7.65  tff(f_187, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 15.01/7.65  tff(f_105, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 15.01/7.65  tff(f_153, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 15.01/7.65  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_2976, plain, (![C_465, A_466, B_467]: (v1_relat_1(C_465) | ~m1_subset_1(C_465, k1_zfmisc_1(k2_zfmisc_1(A_466, B_467))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.01/7.65  tff(c_2984, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_2976])).
% 15.01/7.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.01/7.65  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.01/7.65  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.01/7.65  tff(c_84, plain, (![A_229, B_230]: (k4_xboole_0(A_229, B_230)=A_229 | ~r1_xboole_0(A_229, B_230))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.01/7.65  tff(c_92, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(resolution, [status(thm)], [c_16, c_84])).
% 15.01/7.65  tff(c_3040, plain, (![A_476, B_477]: (k4_xboole_0(A_476, k4_xboole_0(A_476, B_477))=k3_xboole_0(A_476, B_477))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.01/7.65  tff(c_3066, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_92, c_3040])).
% 15.01/7.65  tff(c_3070, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3066])).
% 15.01/7.65  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.01/7.65  tff(c_3071, plain, (![A_478]: (k4_xboole_0(A_478, A_478)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3066])).
% 15.01/7.65  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.01/7.65  tff(c_3076, plain, (![A_478]: (k4_xboole_0(A_478, k1_xboole_0)=k3_xboole_0(A_478, A_478))), inference(superposition, [status(thm), theory('equality')], [c_3071, c_14])).
% 15.01/7.65  tff(c_3100, plain, (![A_479]: (k3_xboole_0(A_479, A_479)=A_479)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_3076])).
% 15.01/7.65  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.01/7.65  tff(c_17809, plain, (![A_1119, C_1120]: (~r1_xboole_0(A_1119, A_1119) | ~r2_hidden(C_1120, A_1119))), inference(superposition, [status(thm), theory('equality')], [c_3100, c_10])).
% 15.01/7.65  tff(c_17815, plain, (![C_1120, B_16]: (~r2_hidden(C_1120, B_16) | k4_xboole_0(B_16, B_16)!=B_16)), inference(resolution, [status(thm)], [c_20, c_17809])).
% 15.01/7.65  tff(c_17824, plain, (![C_1121, B_1122]: (~r2_hidden(C_1121, B_1122) | k1_xboole_0!=B_1122)), inference(demodulation, [status(thm), theory('equality')], [c_3070, c_17815])).
% 15.01/7.65  tff(c_17832, plain, (![A_1, B_2]: (k1_xboole_0!=A_1 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_17824])).
% 15.01/7.65  tff(c_18317, plain, (![A_1166, B_1167]: (k7_relat_1(A_1166, B_1167)=k1_xboole_0 | ~r1_xboole_0(B_1167, k1_relat_1(A_1166)) | ~v1_relat_1(A_1166))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.01/7.65  tff(c_18349, plain, (![A_1168, A_1169]: (k7_relat_1(A_1168, A_1169)=k1_xboole_0 | ~v1_relat_1(A_1168) | k1_xboole_0!=A_1169)), inference(resolution, [status(thm)], [c_17832, c_18317])).
% 15.01/7.65  tff(c_18356, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2984, c_18349])).
% 15.01/7.65  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_2983, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_2976])).
% 15.01/7.65  tff(c_18366, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2983, c_18349])).
% 15.01/7.65  tff(c_70, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_66, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_62, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_17899, plain, (![A_1129, B_1130]: (r1_xboole_0(A_1129, B_1130) | ~r1_subset_1(A_1129, B_1130) | v1_xboole_0(B_1130) | v1_xboole_0(A_1129))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.01/7.65  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.01/7.65  tff(c_20167, plain, (![A_1305, B_1306]: (k4_xboole_0(A_1305, B_1306)=A_1305 | ~r1_subset_1(A_1305, B_1306) | v1_xboole_0(B_1306) | v1_xboole_0(A_1305))), inference(resolution, [status(thm)], [c_17899, c_18])).
% 15.01/7.65  tff(c_20176, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5' | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_20167])).
% 15.01/7.65  tff(c_20181, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_20176])).
% 15.01/7.65  tff(c_20223, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_20181, c_14])).
% 15.01/7.65  tff(c_20246, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3070, c_20223])).
% 15.01/7.65  tff(c_18470, plain, (![A_1177, B_1178, C_1179]: (k9_subset_1(A_1177, B_1178, C_1179)=k3_xboole_0(B_1178, C_1179) | ~m1_subset_1(C_1179, k1_zfmisc_1(A_1177)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.01/7.65  tff(c_18482, plain, (![B_1178]: (k9_subset_1('#skF_3', B_1178, '#skF_6')=k3_xboole_0(B_1178, '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_18470])).
% 15.01/7.65  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_58, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_72, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_52, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_18838, plain, (![C_1207, D_1204, B_1202, F_1203, A_1205, E_1206]: (v1_funct_1(k1_tmap_1(A_1205, B_1202, C_1207, D_1204, E_1206, F_1203)) | ~m1_subset_1(F_1203, k1_zfmisc_1(k2_zfmisc_1(D_1204, B_1202))) | ~v1_funct_2(F_1203, D_1204, B_1202) | ~v1_funct_1(F_1203) | ~m1_subset_1(E_1206, k1_zfmisc_1(k2_zfmisc_1(C_1207, B_1202))) | ~v1_funct_2(E_1206, C_1207, B_1202) | ~v1_funct_1(E_1206) | ~m1_subset_1(D_1204, k1_zfmisc_1(A_1205)) | v1_xboole_0(D_1204) | ~m1_subset_1(C_1207, k1_zfmisc_1(A_1205)) | v1_xboole_0(C_1207) | v1_xboole_0(B_1202) | v1_xboole_0(A_1205))), inference(cnfTransformation, [status(thm)], [f_187])).
% 15.01/7.65  tff(c_18842, plain, (![A_1205, C_1207, E_1206]: (v1_funct_1(k1_tmap_1(A_1205, '#skF_4', C_1207, '#skF_6', E_1206, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1206, k1_zfmisc_1(k2_zfmisc_1(C_1207, '#skF_4'))) | ~v1_funct_2(E_1206, C_1207, '#skF_4') | ~v1_funct_1(E_1206) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1205)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1207, k1_zfmisc_1(A_1205)) | v1_xboole_0(C_1207) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1205))), inference(resolution, [status(thm)], [c_50, c_18838])).
% 15.01/7.65  tff(c_18849, plain, (![A_1205, C_1207, E_1206]: (v1_funct_1(k1_tmap_1(A_1205, '#skF_4', C_1207, '#skF_6', E_1206, '#skF_8')) | ~m1_subset_1(E_1206, k1_zfmisc_1(k2_zfmisc_1(C_1207, '#skF_4'))) | ~v1_funct_2(E_1206, C_1207, '#skF_4') | ~v1_funct_1(E_1206) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1205)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1207, k1_zfmisc_1(A_1205)) | v1_xboole_0(C_1207) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1205))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_18842])).
% 15.01/7.65  tff(c_19571, plain, (![A_1266, C_1267, E_1268]: (v1_funct_1(k1_tmap_1(A_1266, '#skF_4', C_1267, '#skF_6', E_1268, '#skF_8')) | ~m1_subset_1(E_1268, k1_zfmisc_1(k2_zfmisc_1(C_1267, '#skF_4'))) | ~v1_funct_2(E_1268, C_1267, '#skF_4') | ~v1_funct_1(E_1268) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1266)) | ~m1_subset_1(C_1267, k1_zfmisc_1(A_1266)) | v1_xboole_0(C_1267) | v1_xboole_0(A_1266))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_18849])).
% 15.01/7.65  tff(c_19576, plain, (![A_1266]: (v1_funct_1(k1_tmap_1(A_1266, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1266)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1266)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1266))), inference(resolution, [status(thm)], [c_56, c_19571])).
% 15.01/7.65  tff(c_19584, plain, (![A_1266]: (v1_funct_1(k1_tmap_1(A_1266, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1266)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1266)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1266))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_19576])).
% 15.01/7.65  tff(c_20089, plain, (![A_1299]: (v1_funct_1(k1_tmap_1(A_1299, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1299)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1299)) | v1_xboole_0(A_1299))), inference(negUnitSimplification, [status(thm)], [c_70, c_19584])).
% 15.01/7.65  tff(c_20092, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_20089])).
% 15.01/7.65  tff(c_20095, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20092])).
% 15.01/7.65  tff(c_20096, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_74, c_20095])).
% 15.01/7.65  tff(c_18687, plain, (![A_1193, B_1194, C_1195, D_1196]: (k2_partfun1(A_1193, B_1194, C_1195, D_1196)=k7_relat_1(C_1195, D_1196) | ~m1_subset_1(C_1195, k1_zfmisc_1(k2_zfmisc_1(A_1193, B_1194))) | ~v1_funct_1(C_1195))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.01/7.65  tff(c_18689, plain, (![D_1196]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1196)=k7_relat_1('#skF_7', D_1196) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_56, c_18687])).
% 15.01/7.65  tff(c_18694, plain, (![D_1196]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1196)=k7_relat_1('#skF_7', D_1196))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_18689])).
% 15.01/7.65  tff(c_18691, plain, (![D_1196]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1196)=k7_relat_1('#skF_8', D_1196) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_50, c_18687])).
% 15.01/7.65  tff(c_18697, plain, (![D_1196]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1196)=k7_relat_1('#skF_8', D_1196))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18691])).
% 15.01/7.65  tff(c_44, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (v1_funct_2(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k4_subset_1(A_162, C_164, D_165), B_163) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_187])).
% 15.01/7.65  tff(c_42, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (m1_subset_1(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162, C_164, D_165), B_163))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_187])).
% 15.01/7.65  tff(c_19730, plain, (![B_1276, C_1278, D_1277, A_1274, F_1273, E_1275]: (k2_partfun1(k4_subset_1(A_1274, C_1278, D_1277), B_1276, k1_tmap_1(A_1274, B_1276, C_1278, D_1277, E_1275, F_1273), C_1278)=E_1275 | ~m1_subset_1(k1_tmap_1(A_1274, B_1276, C_1278, D_1277, E_1275, F_1273), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1274, C_1278, D_1277), B_1276))) | ~v1_funct_2(k1_tmap_1(A_1274, B_1276, C_1278, D_1277, E_1275, F_1273), k4_subset_1(A_1274, C_1278, D_1277), B_1276) | ~v1_funct_1(k1_tmap_1(A_1274, B_1276, C_1278, D_1277, E_1275, F_1273)) | k2_partfun1(D_1277, B_1276, F_1273, k9_subset_1(A_1274, C_1278, D_1277))!=k2_partfun1(C_1278, B_1276, E_1275, k9_subset_1(A_1274, C_1278, D_1277)) | ~m1_subset_1(F_1273, k1_zfmisc_1(k2_zfmisc_1(D_1277, B_1276))) | ~v1_funct_2(F_1273, D_1277, B_1276) | ~v1_funct_1(F_1273) | ~m1_subset_1(E_1275, k1_zfmisc_1(k2_zfmisc_1(C_1278, B_1276))) | ~v1_funct_2(E_1275, C_1278, B_1276) | ~v1_funct_1(E_1275) | ~m1_subset_1(D_1277, k1_zfmisc_1(A_1274)) | v1_xboole_0(D_1277) | ~m1_subset_1(C_1278, k1_zfmisc_1(A_1274)) | v1_xboole_0(C_1278) | v1_xboole_0(B_1276) | v1_xboole_0(A_1274))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.01/7.65  tff(c_34585, plain, (![B_1858, E_1862, D_1860, A_1861, C_1863, F_1859]: (k2_partfun1(k4_subset_1(A_1861, C_1863, D_1860), B_1858, k1_tmap_1(A_1861, B_1858, C_1863, D_1860, E_1862, F_1859), C_1863)=E_1862 | ~v1_funct_2(k1_tmap_1(A_1861, B_1858, C_1863, D_1860, E_1862, F_1859), k4_subset_1(A_1861, C_1863, D_1860), B_1858) | ~v1_funct_1(k1_tmap_1(A_1861, B_1858, C_1863, D_1860, E_1862, F_1859)) | k2_partfun1(D_1860, B_1858, F_1859, k9_subset_1(A_1861, C_1863, D_1860))!=k2_partfun1(C_1863, B_1858, E_1862, k9_subset_1(A_1861, C_1863, D_1860)) | ~m1_subset_1(F_1859, k1_zfmisc_1(k2_zfmisc_1(D_1860, B_1858))) | ~v1_funct_2(F_1859, D_1860, B_1858) | ~v1_funct_1(F_1859) | ~m1_subset_1(E_1862, k1_zfmisc_1(k2_zfmisc_1(C_1863, B_1858))) | ~v1_funct_2(E_1862, C_1863, B_1858) | ~v1_funct_1(E_1862) | ~m1_subset_1(D_1860, k1_zfmisc_1(A_1861)) | v1_xboole_0(D_1860) | ~m1_subset_1(C_1863, k1_zfmisc_1(A_1861)) | v1_xboole_0(C_1863) | v1_xboole_0(B_1858) | v1_xboole_0(A_1861))), inference(resolution, [status(thm)], [c_42, c_19730])).
% 15.01/7.65  tff(c_40806, plain, (![A_2078, F_2076, C_2080, B_2075, E_2079, D_2077]: (k2_partfun1(k4_subset_1(A_2078, C_2080, D_2077), B_2075, k1_tmap_1(A_2078, B_2075, C_2080, D_2077, E_2079, F_2076), C_2080)=E_2079 | ~v1_funct_1(k1_tmap_1(A_2078, B_2075, C_2080, D_2077, E_2079, F_2076)) | k2_partfun1(D_2077, B_2075, F_2076, k9_subset_1(A_2078, C_2080, D_2077))!=k2_partfun1(C_2080, B_2075, E_2079, k9_subset_1(A_2078, C_2080, D_2077)) | ~m1_subset_1(F_2076, k1_zfmisc_1(k2_zfmisc_1(D_2077, B_2075))) | ~v1_funct_2(F_2076, D_2077, B_2075) | ~v1_funct_1(F_2076) | ~m1_subset_1(E_2079, k1_zfmisc_1(k2_zfmisc_1(C_2080, B_2075))) | ~v1_funct_2(E_2079, C_2080, B_2075) | ~v1_funct_1(E_2079) | ~m1_subset_1(D_2077, k1_zfmisc_1(A_2078)) | v1_xboole_0(D_2077) | ~m1_subset_1(C_2080, k1_zfmisc_1(A_2078)) | v1_xboole_0(C_2080) | v1_xboole_0(B_2075) | v1_xboole_0(A_2078))), inference(resolution, [status(thm)], [c_44, c_34585])).
% 15.01/7.65  tff(c_40812, plain, (![A_2078, C_2080, E_2079]: (k2_partfun1(k4_subset_1(A_2078, C_2080, '#skF_6'), '#skF_4', k1_tmap_1(A_2078, '#skF_4', C_2080, '#skF_6', E_2079, '#skF_8'), C_2080)=E_2079 | ~v1_funct_1(k1_tmap_1(A_2078, '#skF_4', C_2080, '#skF_6', E_2079, '#skF_8')) | k2_partfun1(C_2080, '#skF_4', E_2079, k9_subset_1(A_2078, C_2080, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_2078, C_2080, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_2079, k1_zfmisc_1(k2_zfmisc_1(C_2080, '#skF_4'))) | ~v1_funct_2(E_2079, C_2080, '#skF_4') | ~v1_funct_1(E_2079) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2078)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_2080, k1_zfmisc_1(A_2078)) | v1_xboole_0(C_2080) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2078))), inference(resolution, [status(thm)], [c_50, c_40806])).
% 15.01/7.65  tff(c_40820, plain, (![A_2078, C_2080, E_2079]: (k2_partfun1(k4_subset_1(A_2078, C_2080, '#skF_6'), '#skF_4', k1_tmap_1(A_2078, '#skF_4', C_2080, '#skF_6', E_2079, '#skF_8'), C_2080)=E_2079 | ~v1_funct_1(k1_tmap_1(A_2078, '#skF_4', C_2080, '#skF_6', E_2079, '#skF_8')) | k2_partfun1(C_2080, '#skF_4', E_2079, k9_subset_1(A_2078, C_2080, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2078, C_2080, '#skF_6')) | ~m1_subset_1(E_2079, k1_zfmisc_1(k2_zfmisc_1(C_2080, '#skF_4'))) | ~v1_funct_2(E_2079, C_2080, '#skF_4') | ~v1_funct_1(E_2079) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2078)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_2080, k1_zfmisc_1(A_2078)) | v1_xboole_0(C_2080) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2078))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_18697, c_40812])).
% 15.01/7.65  tff(c_47460, plain, (![A_2207, C_2208, E_2209]: (k2_partfun1(k4_subset_1(A_2207, C_2208, '#skF_6'), '#skF_4', k1_tmap_1(A_2207, '#skF_4', C_2208, '#skF_6', E_2209, '#skF_8'), C_2208)=E_2209 | ~v1_funct_1(k1_tmap_1(A_2207, '#skF_4', C_2208, '#skF_6', E_2209, '#skF_8')) | k2_partfun1(C_2208, '#skF_4', E_2209, k9_subset_1(A_2207, C_2208, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2207, C_2208, '#skF_6')) | ~m1_subset_1(E_2209, k1_zfmisc_1(k2_zfmisc_1(C_2208, '#skF_4'))) | ~v1_funct_2(E_2209, C_2208, '#skF_4') | ~v1_funct_1(E_2209) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2207)) | ~m1_subset_1(C_2208, k1_zfmisc_1(A_2207)) | v1_xboole_0(C_2208) | v1_xboole_0(A_2207))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_40820])).
% 15.01/7.65  tff(c_47465, plain, (![A_2207]: (k2_partfun1(k4_subset_1(A_2207, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2207, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2207, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_2207, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2207, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2207)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2207)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2207))), inference(resolution, [status(thm)], [c_56, c_47460])).
% 15.01/7.65  tff(c_47473, plain, (![A_2207]: (k2_partfun1(k4_subset_1(A_2207, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2207, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2207, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_2207, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2207, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2207)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2207)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2207))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_18694, c_47465])).
% 15.01/7.65  tff(c_48125, plain, (![A_2215]: (k2_partfun1(k4_subset_1(A_2215, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2215, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2215, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_2215, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2215, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2215)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2215)) | v1_xboole_0(A_2215))), inference(negUnitSimplification, [status(thm)], [c_70, c_47473])).
% 15.01/7.65  tff(c_3165, plain, (![A_484, C_485]: (~r1_xboole_0(A_484, A_484) | ~r2_hidden(C_485, A_484))), inference(superposition, [status(thm), theory('equality')], [c_3100, c_10])).
% 15.01/7.65  tff(c_3171, plain, (![C_485, B_16]: (~r2_hidden(C_485, B_16) | k4_xboole_0(B_16, B_16)!=B_16)), inference(resolution, [status(thm)], [c_20, c_3165])).
% 15.01/7.65  tff(c_3180, plain, (![C_486, B_487]: (~r2_hidden(C_486, B_487) | k1_xboole_0!=B_487)), inference(demodulation, [status(thm), theory('equality')], [c_3070, c_3171])).
% 15.01/7.65  tff(c_3188, plain, (![A_1, B_2]: (k1_xboole_0!=A_1 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_3180])).
% 15.01/7.65  tff(c_3533, plain, (![A_520, B_521]: (k7_relat_1(A_520, B_521)=k1_xboole_0 | ~r1_xboole_0(B_521, k1_relat_1(A_520)) | ~v1_relat_1(A_520))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.01/7.65  tff(c_3561, plain, (![A_524, A_525]: (k7_relat_1(A_524, A_525)=k1_xboole_0 | ~v1_relat_1(A_524) | k1_xboole_0!=A_525)), inference(resolution, [status(thm)], [c_3188, c_3533])).
% 15.01/7.65  tff(c_3568, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2984, c_3561])).
% 15.01/7.65  tff(c_3578, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2983, c_3561])).
% 15.01/7.65  tff(c_3255, plain, (![A_494, B_495]: (r1_xboole_0(A_494, B_495) | ~r1_subset_1(A_494, B_495) | v1_xboole_0(B_495) | v1_xboole_0(A_494))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.01/7.65  tff(c_5220, plain, (![A_657, B_658]: (k4_xboole_0(A_657, B_658)=A_657 | ~r1_subset_1(A_657, B_658) | v1_xboole_0(B_658) | v1_xboole_0(A_657))), inference(resolution, [status(thm)], [c_3255, c_18])).
% 15.01/7.65  tff(c_5229, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5' | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_5220])).
% 15.01/7.65  tff(c_5234, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_5229])).
% 15.01/7.65  tff(c_5270, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5234, c_14])).
% 15.01/7.65  tff(c_5289, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3070, c_5270])).
% 15.01/7.65  tff(c_3710, plain, (![A_535, B_536, C_537]: (k9_subset_1(A_535, B_536, C_537)=k3_xboole_0(B_536, C_537) | ~m1_subset_1(C_537, k1_zfmisc_1(A_535)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.01/7.65  tff(c_3722, plain, (![B_536]: (k9_subset_1('#skF_3', B_536, '#skF_6')=k3_xboole_0(B_536, '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_3710])).
% 15.01/7.65  tff(c_3896, plain, (![C_558, D_555, A_556, F_554, B_553, E_557]: (v1_funct_1(k1_tmap_1(A_556, B_553, C_558, D_555, E_557, F_554)) | ~m1_subset_1(F_554, k1_zfmisc_1(k2_zfmisc_1(D_555, B_553))) | ~v1_funct_2(F_554, D_555, B_553) | ~v1_funct_1(F_554) | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(C_558, B_553))) | ~v1_funct_2(E_557, C_558, B_553) | ~v1_funct_1(E_557) | ~m1_subset_1(D_555, k1_zfmisc_1(A_556)) | v1_xboole_0(D_555) | ~m1_subset_1(C_558, k1_zfmisc_1(A_556)) | v1_xboole_0(C_558) | v1_xboole_0(B_553) | v1_xboole_0(A_556))), inference(cnfTransformation, [status(thm)], [f_187])).
% 15.01/7.65  tff(c_3900, plain, (![A_556, C_558, E_557]: (v1_funct_1(k1_tmap_1(A_556, '#skF_4', C_558, '#skF_6', E_557, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(C_558, '#skF_4'))) | ~v1_funct_2(E_557, C_558, '#skF_4') | ~v1_funct_1(E_557) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_556)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_558, k1_zfmisc_1(A_556)) | v1_xboole_0(C_558) | v1_xboole_0('#skF_4') | v1_xboole_0(A_556))), inference(resolution, [status(thm)], [c_50, c_3896])).
% 15.01/7.65  tff(c_3907, plain, (![A_556, C_558, E_557]: (v1_funct_1(k1_tmap_1(A_556, '#skF_4', C_558, '#skF_6', E_557, '#skF_8')) | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(C_558, '#skF_4'))) | ~v1_funct_2(E_557, C_558, '#skF_4') | ~v1_funct_1(E_557) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_556)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_558, k1_zfmisc_1(A_556)) | v1_xboole_0(C_558) | v1_xboole_0('#skF_4') | v1_xboole_0(A_556))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3900])).
% 15.01/7.65  tff(c_3969, plain, (![A_563, C_564, E_565]: (v1_funct_1(k1_tmap_1(A_563, '#skF_4', C_564, '#skF_6', E_565, '#skF_8')) | ~m1_subset_1(E_565, k1_zfmisc_1(k2_zfmisc_1(C_564, '#skF_4'))) | ~v1_funct_2(E_565, C_564, '#skF_4') | ~v1_funct_1(E_565) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_563)) | ~m1_subset_1(C_564, k1_zfmisc_1(A_563)) | v1_xboole_0(C_564) | v1_xboole_0(A_563))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_3907])).
% 15.01/7.65  tff(c_3971, plain, (![A_563]: (v1_funct_1(k1_tmap_1(A_563, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_563)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_563)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_563))), inference(resolution, [status(thm)], [c_56, c_3969])).
% 15.01/7.65  tff(c_3976, plain, (![A_563]: (v1_funct_1(k1_tmap_1(A_563, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_563)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_563)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_563))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3971])).
% 15.01/7.65  tff(c_4313, plain, (![A_601]: (v1_funct_1(k1_tmap_1(A_601, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_601)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_601)) | v1_xboole_0(A_601))), inference(negUnitSimplification, [status(thm)], [c_70, c_3976])).
% 15.01/7.65  tff(c_4316, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_4313])).
% 15.01/7.65  tff(c_4319, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4316])).
% 15.01/7.65  tff(c_4320, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_74, c_4319])).
% 15.01/7.65  tff(c_3769, plain, (![A_543, B_544, C_545, D_546]: (k2_partfun1(A_543, B_544, C_545, D_546)=k7_relat_1(C_545, D_546) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(A_543, B_544))) | ~v1_funct_1(C_545))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.01/7.65  tff(c_3771, plain, (![D_546]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_546)=k7_relat_1('#skF_7', D_546) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_56, c_3769])).
% 15.01/7.65  tff(c_3776, plain, (![D_546]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_546)=k7_relat_1('#skF_7', D_546))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3771])).
% 15.01/7.65  tff(c_3773, plain, (![D_546]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_546)=k7_relat_1('#skF_8', D_546) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_50, c_3769])).
% 15.01/7.65  tff(c_3779, plain, (![D_546]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_546)=k7_relat_1('#skF_8', D_546))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3773])).
% 15.01/7.65  tff(c_4895, plain, (![E_631, C_634, D_633, A_630, B_632, F_629]: (k2_partfun1(k4_subset_1(A_630, C_634, D_633), B_632, k1_tmap_1(A_630, B_632, C_634, D_633, E_631, F_629), D_633)=F_629 | ~m1_subset_1(k1_tmap_1(A_630, B_632, C_634, D_633, E_631, F_629), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_630, C_634, D_633), B_632))) | ~v1_funct_2(k1_tmap_1(A_630, B_632, C_634, D_633, E_631, F_629), k4_subset_1(A_630, C_634, D_633), B_632) | ~v1_funct_1(k1_tmap_1(A_630, B_632, C_634, D_633, E_631, F_629)) | k2_partfun1(D_633, B_632, F_629, k9_subset_1(A_630, C_634, D_633))!=k2_partfun1(C_634, B_632, E_631, k9_subset_1(A_630, C_634, D_633)) | ~m1_subset_1(F_629, k1_zfmisc_1(k2_zfmisc_1(D_633, B_632))) | ~v1_funct_2(F_629, D_633, B_632) | ~v1_funct_1(F_629) | ~m1_subset_1(E_631, k1_zfmisc_1(k2_zfmisc_1(C_634, B_632))) | ~v1_funct_2(E_631, C_634, B_632) | ~v1_funct_1(E_631) | ~m1_subset_1(D_633, k1_zfmisc_1(A_630)) | v1_xboole_0(D_633) | ~m1_subset_1(C_634, k1_zfmisc_1(A_630)) | v1_xboole_0(C_634) | v1_xboole_0(B_632) | v1_xboole_0(A_630))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.01/7.65  tff(c_8156, plain, (![D_803, F_802, B_801, C_806, E_805, A_804]: (k2_partfun1(k4_subset_1(A_804, C_806, D_803), B_801, k1_tmap_1(A_804, B_801, C_806, D_803, E_805, F_802), D_803)=F_802 | ~v1_funct_2(k1_tmap_1(A_804, B_801, C_806, D_803, E_805, F_802), k4_subset_1(A_804, C_806, D_803), B_801) | ~v1_funct_1(k1_tmap_1(A_804, B_801, C_806, D_803, E_805, F_802)) | k2_partfun1(D_803, B_801, F_802, k9_subset_1(A_804, C_806, D_803))!=k2_partfun1(C_806, B_801, E_805, k9_subset_1(A_804, C_806, D_803)) | ~m1_subset_1(F_802, k1_zfmisc_1(k2_zfmisc_1(D_803, B_801))) | ~v1_funct_2(F_802, D_803, B_801) | ~v1_funct_1(F_802) | ~m1_subset_1(E_805, k1_zfmisc_1(k2_zfmisc_1(C_806, B_801))) | ~v1_funct_2(E_805, C_806, B_801) | ~v1_funct_1(E_805) | ~m1_subset_1(D_803, k1_zfmisc_1(A_804)) | v1_xboole_0(D_803) | ~m1_subset_1(C_806, k1_zfmisc_1(A_804)) | v1_xboole_0(C_806) | v1_xboole_0(B_801) | v1_xboole_0(A_804))), inference(resolution, [status(thm)], [c_42, c_4895])).
% 15.01/7.65  tff(c_15351, plain, (![F_1039, E_1042, C_1043, D_1040, B_1038, A_1041]: (k2_partfun1(k4_subset_1(A_1041, C_1043, D_1040), B_1038, k1_tmap_1(A_1041, B_1038, C_1043, D_1040, E_1042, F_1039), D_1040)=F_1039 | ~v1_funct_1(k1_tmap_1(A_1041, B_1038, C_1043, D_1040, E_1042, F_1039)) | k2_partfun1(D_1040, B_1038, F_1039, k9_subset_1(A_1041, C_1043, D_1040))!=k2_partfun1(C_1043, B_1038, E_1042, k9_subset_1(A_1041, C_1043, D_1040)) | ~m1_subset_1(F_1039, k1_zfmisc_1(k2_zfmisc_1(D_1040, B_1038))) | ~v1_funct_2(F_1039, D_1040, B_1038) | ~v1_funct_1(F_1039) | ~m1_subset_1(E_1042, k1_zfmisc_1(k2_zfmisc_1(C_1043, B_1038))) | ~v1_funct_2(E_1042, C_1043, B_1038) | ~v1_funct_1(E_1042) | ~m1_subset_1(D_1040, k1_zfmisc_1(A_1041)) | v1_xboole_0(D_1040) | ~m1_subset_1(C_1043, k1_zfmisc_1(A_1041)) | v1_xboole_0(C_1043) | v1_xboole_0(B_1038) | v1_xboole_0(A_1041))), inference(resolution, [status(thm)], [c_44, c_8156])).
% 15.01/7.65  tff(c_15357, plain, (![A_1041, C_1043, E_1042]: (k2_partfun1(k4_subset_1(A_1041, C_1043, '#skF_6'), '#skF_4', k1_tmap_1(A_1041, '#skF_4', C_1043, '#skF_6', E_1042, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1041, '#skF_4', C_1043, '#skF_6', E_1042, '#skF_8')) | k2_partfun1(C_1043, '#skF_4', E_1042, k9_subset_1(A_1041, C_1043, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_1041, C_1043, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1042, k1_zfmisc_1(k2_zfmisc_1(C_1043, '#skF_4'))) | ~v1_funct_2(E_1042, C_1043, '#skF_4') | ~v1_funct_1(E_1042) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1041)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1043, k1_zfmisc_1(A_1041)) | v1_xboole_0(C_1043) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1041))), inference(resolution, [status(thm)], [c_50, c_15351])).
% 15.01/7.65  tff(c_15365, plain, (![A_1041, C_1043, E_1042]: (k2_partfun1(k4_subset_1(A_1041, C_1043, '#skF_6'), '#skF_4', k1_tmap_1(A_1041, '#skF_4', C_1043, '#skF_6', E_1042, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1041, '#skF_4', C_1043, '#skF_6', E_1042, '#skF_8')) | k2_partfun1(C_1043, '#skF_4', E_1042, k9_subset_1(A_1041, C_1043, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1041, C_1043, '#skF_6')) | ~m1_subset_1(E_1042, k1_zfmisc_1(k2_zfmisc_1(C_1043, '#skF_4'))) | ~v1_funct_2(E_1042, C_1043, '#skF_4') | ~v1_funct_1(E_1042) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1041)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1043, k1_zfmisc_1(A_1041)) | v1_xboole_0(C_1043) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1041))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3779, c_15357])).
% 15.01/7.65  tff(c_16686, plain, (![A_1097, C_1098, E_1099]: (k2_partfun1(k4_subset_1(A_1097, C_1098, '#skF_6'), '#skF_4', k1_tmap_1(A_1097, '#skF_4', C_1098, '#skF_6', E_1099, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1097, '#skF_4', C_1098, '#skF_6', E_1099, '#skF_8')) | k2_partfun1(C_1098, '#skF_4', E_1099, k9_subset_1(A_1097, C_1098, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1097, C_1098, '#skF_6')) | ~m1_subset_1(E_1099, k1_zfmisc_1(k2_zfmisc_1(C_1098, '#skF_4'))) | ~v1_funct_2(E_1099, C_1098, '#skF_4') | ~v1_funct_1(E_1099) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1097)) | ~m1_subset_1(C_1098, k1_zfmisc_1(A_1097)) | v1_xboole_0(C_1098) | v1_xboole_0(A_1097))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_15365])).
% 15.01/7.65  tff(c_16691, plain, (![A_1097]: (k2_partfun1(k4_subset_1(A_1097, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1097, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1097, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_1097, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1097, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1097)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1097)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1097))), inference(resolution, [status(thm)], [c_56, c_16686])).
% 15.01/7.65  tff(c_16699, plain, (![A_1097]: (k2_partfun1(k4_subset_1(A_1097, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1097, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1097, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1097, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1097, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1097)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1097)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1097))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3776, c_16691])).
% 15.01/7.65  tff(c_17779, plain, (![A_1118]: (k2_partfun1(k4_subset_1(A_1118, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1118, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1118, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1118, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1118, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1118)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1118)) | v1_xboole_0(A_1118))), inference(negUnitSimplification, [status(thm)], [c_70, c_16699])).
% 15.01/7.65  tff(c_205, plain, (![C_246, A_247, B_248]: (v1_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.01/7.65  tff(c_213, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_205])).
% 15.01/7.65  tff(c_214, plain, (![A_249, B_250]: (r2_hidden('#skF_1'(A_249, B_250), A_249) | r1_xboole_0(A_249, B_250))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.01/7.65  tff(c_124, plain, (![A_234, B_235]: (k4_xboole_0(A_234, k4_xboole_0(A_234, B_235))=k3_xboole_0(A_234, B_235))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.01/7.65  tff(c_139, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_92, c_124])).
% 15.01/7.65  tff(c_142, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_139])).
% 15.01/7.65  tff(c_150, plain, (![A_240]: (k4_xboole_0(A_240, A_240)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_139])).
% 15.01/7.65  tff(c_155, plain, (![A_240]: (k4_xboole_0(A_240, k1_xboole_0)=k3_xboole_0(A_240, A_240))), inference(superposition, [status(thm), theory('equality')], [c_150, c_14])).
% 15.01/7.65  tff(c_171, plain, (![A_241]: (k3_xboole_0(A_241, A_241)=A_241)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_155])).
% 15.01/7.65  tff(c_193, plain, (![A_242, C_243]: (~r1_xboole_0(A_242, A_242) | ~r2_hidden(C_243, A_242))), inference(superposition, [status(thm), theory('equality')], [c_171, c_10])).
% 15.01/7.65  tff(c_196, plain, (![C_243, B_16]: (~r2_hidden(C_243, B_16) | k4_xboole_0(B_16, B_16)!=B_16)), inference(resolution, [status(thm)], [c_20, c_193])).
% 15.01/7.65  tff(c_201, plain, (![C_243, B_16]: (~r2_hidden(C_243, B_16) | k1_xboole_0!=B_16)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_196])).
% 15.01/7.65  tff(c_226, plain, (![A_249, B_250]: (k1_xboole_0!=A_249 | r1_xboole_0(A_249, B_250))), inference(resolution, [status(thm)], [c_214, c_201])).
% 15.01/7.65  tff(c_459, plain, (![A_269, B_270]: (k7_relat_1(A_269, B_270)=k1_xboole_0 | ~r1_xboole_0(B_270, k1_relat_1(A_269)) | ~v1_relat_1(A_269))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.01/7.65  tff(c_798, plain, (![A_300, A_301]: (k7_relat_1(A_300, A_301)=k1_xboole_0 | ~v1_relat_1(A_300) | k1_xboole_0!=A_301)), inference(resolution, [status(thm)], [c_226, c_459])).
% 15.01/7.65  tff(c_834, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_213, c_798])).
% 15.01/7.65  tff(c_212, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_205])).
% 15.01/7.65  tff(c_844, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_212, c_798])).
% 15.01/7.65  tff(c_712, plain, (![A_290, B_291]: (r1_xboole_0(A_290, B_291) | ~r1_subset_1(A_290, B_291) | v1_xboole_0(B_291) | v1_xboole_0(A_290))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.01/7.65  tff(c_2873, plain, (![A_461, B_462]: (k4_xboole_0(A_461, B_462)=A_461 | ~r1_subset_1(A_461, B_462) | v1_xboole_0(B_462) | v1_xboole_0(A_461))), inference(resolution, [status(thm)], [c_712, c_18])).
% 15.01/7.65  tff(c_2885, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5' | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2873])).
% 15.01/7.65  tff(c_2891, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_2885])).
% 15.01/7.65  tff(c_2939, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2891, c_14])).
% 15.01/7.65  tff(c_2964, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_142, c_2939])).
% 15.01/7.65  tff(c_922, plain, (![A_315, B_316, C_317, D_318]: (k2_partfun1(A_315, B_316, C_317, D_318)=k7_relat_1(C_317, D_318) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))) | ~v1_funct_1(C_317))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.01/7.65  tff(c_926, plain, (![D_318]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_318)=k7_relat_1('#skF_8', D_318) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_50, c_922])).
% 15.01/7.65  tff(c_932, plain, (![D_318]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_318)=k7_relat_1('#skF_8', D_318))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_926])).
% 15.01/7.65  tff(c_924, plain, (![D_318]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_318)=k7_relat_1('#skF_7', D_318) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_56, c_922])).
% 15.01/7.65  tff(c_929, plain, (![D_318]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_318)=k7_relat_1('#skF_7', D_318))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_924])).
% 15.01/7.65  tff(c_872, plain, (![A_308, B_309, C_310]: (k9_subset_1(A_308, B_309, C_310)=k3_xboole_0(B_309, C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(A_308)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.01/7.65  tff(c_884, plain, (![B_309]: (k9_subset_1('#skF_3', B_309, '#skF_6')=k3_xboole_0(B_309, '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_872])).
% 15.01/7.65  tff(c_48, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.01/7.65  tff(c_121, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_48])).
% 15.01/7.65  tff(c_894, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_884, c_884, c_121])).
% 15.01/7.65  tff(c_1016, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_932, c_929, c_894])).
% 15.01/7.65  tff(c_2967, plain, (k7_relat_1('#skF_7', k1_xboole_0)!=k7_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2964, c_2964, c_1016])).
% 15.01/7.65  tff(c_2970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_834, c_844, c_2967])).
% 15.01/7.65  tff(c_2971, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_48])).
% 15.01/7.65  tff(c_3164, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_2971])).
% 15.01/7.65  tff(c_17790, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17779, c_3164])).
% 15.01/7.65  tff(c_17804, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_3568, c_3578, c_5289, c_5289, c_3722, c_3722, c_4320, c_17790])).
% 15.01/7.65  tff(c_17806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_17804])).
% 15.01/7.65  tff(c_17807, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_2971])).
% 15.01/7.65  tff(c_48137, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48125, c_17807])).
% 15.01/7.65  tff(c_48151, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_18356, c_18366, c_20246, c_18482, c_20246, c_18482, c_20096, c_48137])).
% 15.01/7.65  tff(c_48153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_48151])).
% 15.01/7.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.01/7.65  
% 15.01/7.65  Inference rules
% 15.01/7.65  ----------------------
% 15.01/7.65  #Ref     : 0
% 15.01/7.65  #Sup     : 12620
% 15.01/7.65  #Fact    : 0
% 15.01/7.65  #Define  : 0
% 15.01/7.65  #Split   : 26
% 15.01/7.65  #Chain   : 0
% 15.01/7.65  #Close   : 0
% 15.01/7.65  
% 15.01/7.65  Ordering : KBO
% 15.01/7.65  
% 15.01/7.65  Simplification rules
% 15.01/7.65  ----------------------
% 15.01/7.65  #Subsume      : 4936
% 15.01/7.65  #Demod        : 5563
% 15.01/7.65  #Tautology    : 4051
% 15.01/7.65  #SimpNegUnit  : 457
% 15.01/7.65  #BackRed      : 6
% 15.01/7.65  
% 15.01/7.65  #Partial instantiations: 0
% 15.01/7.65  #Strategies tried      : 1
% 15.01/7.65  
% 15.01/7.65  Timing (in seconds)
% 15.01/7.65  ----------------------
% 15.01/7.65  Preprocessing        : 0.43
% 15.01/7.65  Parsing              : 0.22
% 15.01/7.65  CNF conversion       : 0.06
% 15.01/7.65  Main loop            : 6.35
% 15.01/7.65  Inferencing          : 1.36
% 15.01/7.65  Reduction            : 2.37
% 15.01/7.65  Demodulation         : 1.81
% 15.01/7.65  BG Simplification    : 0.14
% 15.01/7.65  Subsumption          : 2.20
% 15.01/7.65  Abstraction          : 0.22
% 15.01/7.65  MUC search           : 0.00
% 15.01/7.65  Cooper               : 0.00
% 15.01/7.65  Total                : 6.85
% 15.01/7.65  Index Insertion      : 0.00
% 15.01/7.65  Index Deletion       : 0.00
% 15.01/7.65  Index Matching       : 0.00
% 15.01/7.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
