%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1464+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:57 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :  359 (4979 expanded)
%              Number of leaves         :   45 (1951 expanded)
%              Depth                    :   29
%              Number of atoms          : 1483 (39103 expanded)
%              Number of equality atoms :    2 ( 138 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v20_lattices > v19_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v3_filter_0 > v2_struct_0 > v1_xboole_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k7_filter_0 > k4_lattices > k4_filter_0 > k3_lattices > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(k4_filter_0,type,(
    k4_filter_0: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_filter_0,type,(
    k7_filter_0: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v20_lattices,type,(
    v20_lattices: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v19_lattices,type,(
    v19_lattices: ( $i * $i ) > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v3_filter_0,type,(
    v3_filter_0: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_297,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v3_filter_0(A)
          & l3_lattices(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v19_lattices(B,A)
              & v20_lattices(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(A))
                           => ( ( r2_hidden(k7_filter_0(A,C,D),B)
                                & r2_hidden(k7_filter_0(A,E,F),B) )
                             => ( r2_hidden(k7_filter_0(A,k3_lattices(A,C,E),k3_lattices(A,D,F)),B)
                                & r2_hidden(k7_filter_0(A,k4_lattices(A,C,E),k4_lattices(A,D,F)),B) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_filter_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_filter_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_filter_0)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v19_lattices(B,A)
            & v20_lattices(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ( r2_hidden(k4_filter_0(A,C,D),B)
                       => ( r2_hidden(k4_filter_0(A,C,k3_lattices(A,D,E)),B)
                          & r2_hidden(k4_filter_0(A,C,k3_lattices(A,E,D)),B)
                          & r2_hidden(k4_filter_0(A,k4_lattices(A,C,E),D),B)
                          & r2_hidden(k4_filter_0(A,k4_lattices(A,E,C),D),B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l66_filter_1)).

tff(f_212,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v19_lattices(B,A)
            & v20_lattices(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ( ( r2_hidden(k4_filter_0(A,C,D),B)
                          & r2_hidden(k4_filter_0(A,C,E),B) )
                       => r2_hidden(k4_filter_0(A,C,k4_lattices(A,D,E)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l70_filter_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_106,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k7_filter_0(A,B,C) = k4_lattices(A,k4_filter_0(A,B,C),k4_filter_0(A,C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_filter_0)).

tff(f_257,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( ( ~ v1_xboole_0(B)
              & v19_lattices(B,A)
              & v20_lattices(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                    <=> r2_hidden(k4_lattices(A,C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_0)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v19_lattices(B,A)
            & v20_lattices(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ( ( r2_hidden(k4_filter_0(A,C,D),B)
                          & r2_hidden(k4_filter_0(A,E,D),B) )
                       => r2_hidden(k4_filter_0(A,k3_lattices(A,C,E),D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_filter_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattices)).

tff(c_142,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_140,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_136,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_120,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_122,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k4_filter_0(A_12,B_13,C_14),u1_struct_0(A_12))
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l3_lattices(A_12)
      | ~ v10_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_134,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_138,plain,(
    v3_filter_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_132,plain,(
    v19_lattices('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_130,plain,(
    v20_lattices('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_128,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_126,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_28,plain,(
    ! [A_19,C_43,B_35,D_47,E_49] :
      ( r2_hidden(k4_filter_0(A_19,k4_lattices(A_19,E_49,C_43),D_47),B_35)
      | ~ r2_hidden(k4_filter_0(A_19,C_43,D_47),B_35)
      | ~ m1_subset_1(E_49,u1_struct_0(A_19))
      | ~ m1_subset_1(D_47,u1_struct_0(A_19))
      | ~ m1_subset_1(C_43,u1_struct_0(A_19))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ v20_lattices(B_35,A_19)
      | ~ v19_lattices(B_35,A_19)
      | v1_xboole_0(B_35)
      | ~ l3_lattices(A_19)
      | ~ v3_filter_0(A_19)
      | ~ v10_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_124,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_1640,plain,(
    ! [B_500,C_499,E_502,D_503,A_501] :
      ( r2_hidden(k4_filter_0(A_501,C_499,k4_lattices(A_501,D_503,E_502)),B_500)
      | ~ r2_hidden(k4_filter_0(A_501,C_499,E_502),B_500)
      | ~ r2_hidden(k4_filter_0(A_501,C_499,D_503),B_500)
      | ~ m1_subset_1(E_502,u1_struct_0(A_501))
      | ~ m1_subset_1(D_503,u1_struct_0(A_501))
      | ~ m1_subset_1(C_499,u1_struct_0(A_501))
      | ~ m1_subset_1(B_500,k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ v20_lattices(B_500,A_501)
      | ~ v19_lattices(B_500,A_501)
      | v1_xboole_0(B_500)
      | ~ l3_lattices(A_501)
      | ~ v3_filter_0(A_501)
      | ~ v10_lattices(A_501)
      | v2_struct_0(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [A_199] :
      ( l1_lattices(A_199)
      | ~ l3_lattices(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_147,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_143])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k4_lattices(A_15,B_16,C_17),u1_struct_0(A_15))
      | ~ m1_subset_1(C_17,u1_struct_0(A_15))
      | ~ m1_subset_1(B_16,u1_struct_0(A_15))
      | ~ l1_lattices(A_15)
      | ~ v6_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_118,plain,(
    r2_hidden(k7_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_16,plain,(
    ! [A_2,B_6,C_8] :
      ( k4_lattices(A_2,k4_filter_0(A_2,B_6,C_8),k4_filter_0(A_2,C_8,B_6)) = k7_filter_0(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | ~ v10_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1051,plain,(
    ! [C_409,B_410,A_411,D_412] :
      ( r2_hidden(C_409,B_410)
      | ~ r2_hidden(k4_lattices(A_411,C_409,D_412),B_410)
      | ~ m1_subset_1(D_412,u1_struct_0(A_411))
      | ~ m1_subset_1(C_409,u1_struct_0(A_411))
      | ~ v20_lattices(B_410,A_411)
      | ~ v19_lattices(B_410,A_411)
      | ~ m1_subset_1(B_410,k1_zfmisc_1(u1_struct_0(A_411)))
      | v1_xboole_0(B_410)
      | ~ l3_lattices(A_411)
      | ~ v10_lattices(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_1262,plain,(
    ! [A_460,B_461,C_462,B_463] :
      ( r2_hidden(k4_filter_0(A_460,B_461,C_462),B_463)
      | ~ r2_hidden(k7_filter_0(A_460,B_461,C_462),B_463)
      | ~ m1_subset_1(k4_filter_0(A_460,C_462,B_461),u1_struct_0(A_460))
      | ~ m1_subset_1(k4_filter_0(A_460,B_461,C_462),u1_struct_0(A_460))
      | ~ v20_lattices(B_463,A_460)
      | ~ v19_lattices(B_463,A_460)
      | ~ m1_subset_1(B_463,k1_zfmisc_1(u1_struct_0(A_460)))
      | v1_xboole_0(B_463)
      | ~ l3_lattices(A_460)
      | ~ v10_lattices(A_460)
      | v2_struct_0(A_460)
      | ~ m1_subset_1(C_462,u1_struct_0(A_460))
      | ~ m1_subset_1(B_461,u1_struct_0(A_460))
      | ~ l3_lattices(A_460)
      | ~ v10_lattices(A_460)
      | v2_struct_0(A_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1051])).

tff(c_1268,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_1262])).

tff(c_1281,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_128,c_132,c_130,c_1268])).

tff(c_1282,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1281])).

tff(c_1346,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1282])).

tff(c_1349,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1346])).

tff(c_1355,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_1349])).

tff(c_1357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1355])).

tff(c_1358,plain,
    ( ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1282])).

tff(c_1360,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1358])).

tff(c_1363,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1360])).

tff(c_1369,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_124,c_126,c_1363])).

tff(c_1371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1369])).

tff(c_1373,plain,(
    m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1358])).

tff(c_1233,plain,(
    ! [E_458,B_456,C_455,D_459,A_457] :
      ( r2_hidden(k4_filter_0(A_457,C_455,k4_lattices(A_457,D_459,E_458)),B_456)
      | ~ r2_hidden(k4_filter_0(A_457,C_455,E_458),B_456)
      | ~ r2_hidden(k4_filter_0(A_457,C_455,D_459),B_456)
      | ~ m1_subset_1(E_458,u1_struct_0(A_457))
      | ~ m1_subset_1(D_459,u1_struct_0(A_457))
      | ~ m1_subset_1(C_455,u1_struct_0(A_457))
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ v20_lattices(B_456,A_457)
      | ~ v19_lattices(B_456,A_457)
      | v1_xboole_0(B_456)
      | ~ l3_lattices(A_457)
      | ~ v3_filter_0(A_457)
      | ~ v10_lattices(A_457)
      | v2_struct_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_1083,plain,(
    ! [A_415,C_416,D_417,B_418] :
      ( r2_hidden(k4_lattices(A_415,C_416,D_417),B_418)
      | ~ r2_hidden(D_417,B_418)
      | ~ r2_hidden(C_416,B_418)
      | ~ m1_subset_1(D_417,u1_struct_0(A_415))
      | ~ m1_subset_1(C_416,u1_struct_0(A_415))
      | ~ v20_lattices(B_418,A_415)
      | ~ v19_lattices(B_418,A_415)
      | ~ m1_subset_1(B_418,k1_zfmisc_1(u1_struct_0(A_415)))
      | v1_xboole_0(B_418)
      | ~ l3_lattices(A_415)
      | ~ v10_lattices(A_415)
      | v2_struct_0(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_1085,plain,(
    ! [C_416,D_417] :
      ( r2_hidden(k4_lattices('#skF_3',C_416,D_417),'#skF_4')
      | ~ r2_hidden(D_417,'#skF_4')
      | ~ r2_hidden(C_416,'#skF_4')
      | ~ m1_subset_1(D_417,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_416,u1_struct_0('#skF_3'))
      | ~ v20_lattices('#skF_4','#skF_3')
      | ~ v19_lattices('#skF_4','#skF_3')
      | v1_xboole_0('#skF_4')
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_128,c_1083])).

tff(c_1088,plain,(
    ! [C_416,D_417] :
      ( r2_hidden(k4_lattices('#skF_3',C_416,D_417),'#skF_4')
      | ~ r2_hidden(D_417,'#skF_4')
      | ~ r2_hidden(C_416,'#skF_4')
      | ~ m1_subset_1(D_417,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_416,u1_struct_0('#skF_3'))
      | v1_xboole_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_132,c_130,c_1085])).

tff(c_1090,plain,(
    ! [C_419,D_420] :
      ( r2_hidden(k4_lattices('#skF_3',C_419,D_420),'#skF_4')
      | ~ r2_hidden(D_420,'#skF_4')
      | ~ r2_hidden(C_419,'#skF_4')
      | ~ m1_subset_1(D_420,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_419,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1088])).

tff(c_1109,plain,(
    ! [B_6,C_8] :
      ( r2_hidden(k7_filter_0('#skF_3',B_6,C_8),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_8,B_6),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_6,C_8),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_8,B_6),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k4_filter_0('#skF_3',B_6,C_8),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1090])).

tff(c_1128,plain,(
    ! [B_6,C_8] :
      ( r2_hidden(k7_filter_0('#skF_3',B_6,C_8),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_8,B_6),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_6,C_8),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_8,B_6),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k4_filter_0('#skF_3',B_6,C_8),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_1109])).

tff(c_1138,plain,(
    ! [B_426,C_427] :
      ( r2_hidden(k7_filter_0('#skF_3',B_426,C_427),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_427,B_426),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_426,C_427),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_427,B_426),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k4_filter_0('#skF_3',B_426,C_427),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_427,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_426,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1128])).

tff(c_1141,plain,(
    ! [C_14,B_13] :
      ( r2_hidden(k7_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_14,B_13),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_1138])).

tff(c_1147,plain,(
    ! [C_14,B_13] :
      ( r2_hidden(k7_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_14,B_13),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_1141])).

tff(c_1150,plain,(
    ! [C_428,B_429] :
      ( r2_hidden(k7_filter_0('#skF_3',C_428,B_429),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_429,C_428),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_428,B_429),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_428,B_429),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_428,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_429,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1147])).

tff(c_1154,plain,(
    ! [B_13,C_14] :
      ( r2_hidden(k7_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_1150])).

tff(c_1160,plain,(
    ! [B_13,C_14] :
      ( r2_hidden(k7_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_1154])).

tff(c_1163,plain,(
    ! [B_430,C_431] :
      ( r2_hidden(k7_filter_0('#skF_3',B_430,C_431),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_431,B_430),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_430,C_431),'#skF_4')
      | ~ m1_subset_1(C_431,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_430,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1160])).

tff(c_32,plain,(
    ! [A_19,C_43,B_35,D_47,E_49] :
      ( r2_hidden(k4_filter_0(A_19,C_43,k3_lattices(A_19,E_49,D_47)),B_35)
      | ~ r2_hidden(k4_filter_0(A_19,C_43,D_47),B_35)
      | ~ m1_subset_1(E_49,u1_struct_0(A_19))
      | ~ m1_subset_1(D_47,u1_struct_0(A_19))
      | ~ m1_subset_1(C_43,u1_struct_0(A_19))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ v20_lattices(B_35,A_19)
      | ~ v19_lattices(B_35,A_19)
      | v1_xboole_0(B_35)
      | ~ l3_lattices(A_19)
      | ~ v3_filter_0(A_19)
      | ~ v10_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_746,plain,(
    ! [D_335,E_334,A_333,B_337,C_336] :
      ( r2_hidden(k4_filter_0(A_333,k3_lattices(A_333,C_336,E_334),D_335),B_337)
      | ~ r2_hidden(k4_filter_0(A_333,E_334,D_335),B_337)
      | ~ r2_hidden(k4_filter_0(A_333,C_336,D_335),B_337)
      | ~ m1_subset_1(E_334,u1_struct_0(A_333))
      | ~ m1_subset_1(D_335,u1_struct_0(A_333))
      | ~ m1_subset_1(C_336,u1_struct_0(A_333))
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ v20_lattices(B_337,A_333)
      | ~ v19_lattices(B_337,A_333)
      | v1_xboole_0(B_337)
      | ~ l3_lattices(A_333)
      | ~ v3_filter_0(A_333)
      | ~ v10_lattices(A_333)
      | v2_struct_0(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_148,plain,(
    ! [A_200] :
      ( l2_lattices(A_200)
      | ~ l3_lattices(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_152,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_148])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k3_lattices(A_9,B_10,C_11),u1_struct_0(A_9))
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l2_lattices(A_9)
      | ~ v4_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_277,plain,(
    ! [A_253,C_254,D_255,B_256] :
      ( r2_hidden(k4_lattices(A_253,C_254,D_255),B_256)
      | ~ r2_hidden(D_255,B_256)
      | ~ r2_hidden(C_254,B_256)
      | ~ m1_subset_1(D_255,u1_struct_0(A_253))
      | ~ m1_subset_1(C_254,u1_struct_0(A_253))
      | ~ v20_lattices(B_256,A_253)
      | ~ v19_lattices(B_256,A_253)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_253)))
      | v1_xboole_0(B_256)
      | ~ l3_lattices(A_253)
      | ~ v10_lattices(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_279,plain,(
    ! [C_254,D_255] :
      ( r2_hidden(k4_lattices('#skF_3',C_254,D_255),'#skF_4')
      | ~ r2_hidden(D_255,'#skF_4')
      | ~ r2_hidden(C_254,'#skF_4')
      | ~ m1_subset_1(D_255,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_3'))
      | ~ v20_lattices('#skF_4','#skF_3')
      | ~ v19_lattices('#skF_4','#skF_3')
      | v1_xboole_0('#skF_4')
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_128,c_277])).

tff(c_282,plain,(
    ! [C_254,D_255] :
      ( r2_hidden(k4_lattices('#skF_3',C_254,D_255),'#skF_4')
      | ~ r2_hidden(D_255,'#skF_4')
      | ~ r2_hidden(C_254,'#skF_4')
      | ~ m1_subset_1(D_255,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_3'))
      | v1_xboole_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_132,c_130,c_279])).

tff(c_284,plain,(
    ! [C_257,D_258] :
      ( r2_hidden(k4_lattices('#skF_3',C_257,D_258),'#skF_4')
      | ~ r2_hidden(D_258,'#skF_4')
      | ~ r2_hidden(C_257,'#skF_4')
      | ~ m1_subset_1(D_258,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_257,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_282])).

tff(c_303,plain,(
    ! [B_6,C_8] :
      ( r2_hidden(k7_filter_0('#skF_3',B_6,C_8),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_8,B_6),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_6,C_8),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_8,B_6),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k4_filter_0('#skF_3',B_6,C_8),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_284])).

tff(c_322,plain,(
    ! [B_6,C_8] :
      ( r2_hidden(k7_filter_0('#skF_3',B_6,C_8),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_8,B_6),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_6,C_8),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_8,B_6),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k4_filter_0('#skF_3',B_6,C_8),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_8,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_6,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_303])).

tff(c_324,plain,(
    ! [B_259,C_260] :
      ( r2_hidden(k7_filter_0('#skF_3',B_259,C_260),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_260,B_259),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_259,C_260),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_260,B_259),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k4_filter_0('#skF_3',B_259,C_260),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_260,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_259,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_322])).

tff(c_327,plain,(
    ! [C_14,B_13] :
      ( r2_hidden(k7_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_14,B_13),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_324])).

tff(c_333,plain,(
    ! [C_14,B_13] :
      ( r2_hidden(k7_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_14,B_13),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_327])).

tff(c_336,plain,(
    ! [C_261,B_262] :
      ( r2_hidden(k7_filter_0('#skF_3',C_261,B_262),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_262,C_261),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_261,B_262),'#skF_4')
      | ~ m1_subset_1(k4_filter_0('#skF_3',C_261,B_262),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_261,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_262,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_333])).

tff(c_340,plain,(
    ! [B_13,C_14] :
      ( r2_hidden(k7_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_336])).

tff(c_346,plain,(
    ! [B_13,C_14] :
      ( r2_hidden(k7_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_14,B_13),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_13,C_14),'#skF_4')
      | ~ m1_subset_1(C_14,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_340])).

tff(c_349,plain,(
    ! [B_263,C_264] :
      ( r2_hidden(k7_filter_0('#skF_3',B_263,C_264),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',C_264,B_263),'#skF_4')
      | ~ r2_hidden(k4_filter_0('#skF_3',B_263,C_264),'#skF_4')
      | ~ m1_subset_1(C_264,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_263,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_346])).

tff(c_114,plain,
    ( ~ r2_hidden(k7_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ r2_hidden(k7_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_162,plain,(
    ~ r2_hidden(k7_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_356,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_6','#skF_8'),k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_349,c_162])).

tff(c_358,plain,(
    ~ m1_subset_1(k3_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_361,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_358])).

tff(c_367,plain,
    ( ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_126,c_122,c_361])).

tff(c_368,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_367])).

tff(c_372,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_368])).

tff(c_375,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_140,c_372])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_375])).

tff(c_379,plain,(
    m1_subset_1(k3_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_34,plain,(
    ! [A_19,C_43,B_35,D_47,E_49] :
      ( r2_hidden(k4_filter_0(A_19,C_43,k3_lattices(A_19,D_47,E_49)),B_35)
      | ~ r2_hidden(k4_filter_0(A_19,C_43,D_47),B_35)
      | ~ m1_subset_1(E_49,u1_struct_0(A_19))
      | ~ m1_subset_1(D_47,u1_struct_0(A_19))
      | ~ m1_subset_1(C_43,u1_struct_0(A_19))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ v20_lattices(B_35,A_19)
      | ~ v19_lattices(B_35,A_19)
      | v1_xboole_0(B_35)
      | ~ l3_lattices(A_19)
      | ~ v3_filter_0(A_19)
      | ~ v10_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_444,plain,(
    ! [B_292,A_288,E_289,D_290,C_291] :
      ( r2_hidden(k4_filter_0(A_288,k3_lattices(A_288,C_291,E_289),D_290),B_292)
      | ~ r2_hidden(k4_filter_0(A_288,E_289,D_290),B_292)
      | ~ r2_hidden(k4_filter_0(A_288,C_291,D_290),B_292)
      | ~ m1_subset_1(E_289,u1_struct_0(A_288))
      | ~ m1_subset_1(D_290,u1_struct_0(A_288))
      | ~ m1_subset_1(C_291,u1_struct_0(A_288))
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ v20_lattices(B_292,A_288)
      | ~ v19_lattices(B_292,A_288)
      | v1_xboole_0(B_292)
      | ~ l3_lattices(A_288)
      | ~ v3_filter_0(A_288)
      | ~ v10_lattices(A_288)
      | v2_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_389,plain,(
    ! [E_274,A_272,C_270,D_271,B_273] :
      ( r2_hidden(k4_filter_0(A_272,C_270,k3_lattices(A_272,D_271,E_274)),B_273)
      | ~ r2_hidden(k4_filter_0(A_272,C_270,D_271),B_273)
      | ~ m1_subset_1(E_274,u1_struct_0(A_272))
      | ~ m1_subset_1(D_271,u1_struct_0(A_272))
      | ~ m1_subset_1(C_270,u1_struct_0(A_272))
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ v20_lattices(B_273,A_272)
      | ~ v19_lattices(B_273,A_272)
      | v1_xboole_0(B_273)
      | ~ l3_lattices(A_272)
      | ~ v3_filter_0(A_272)
      | ~ v10_lattices(A_272)
      | v2_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_378,plain,
    ( ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_6','#skF_8'),k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_388,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_6','#skF_8'),k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_392,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_389,c_388])).

tff(c_398,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_126,c_122,c_392])).

tff(c_399,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_398])).

tff(c_401,plain,(
    ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_404,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_401])).

tff(c_410,plain,
    ( ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_124,c_120,c_404])).

tff(c_411,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_410])).

tff(c_415,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_411])).

tff(c_418,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_140,c_415])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_418])).

tff(c_421,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_450,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_5'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_444,c_421])).

tff(c_463,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_5'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_124,c_126,c_120,c_450])).

tff(c_464,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_5'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_463])).

tff(c_471,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_213,plain,(
    ! [D_241,B_242,A_243,C_244] :
      ( r2_hidden(D_241,B_242)
      | ~ r2_hidden(k4_lattices(A_243,C_244,D_241),B_242)
      | ~ m1_subset_1(D_241,u1_struct_0(A_243))
      | ~ m1_subset_1(C_244,u1_struct_0(A_243))
      | ~ v20_lattices(B_242,A_243)
      | ~ v19_lattices(B_242,A_243)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_243)))
      | v1_xboole_0(B_242)
      | ~ l3_lattices(A_243)
      | ~ v10_lattices(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_495,plain,(
    ! [A_298,C_299,B_300,B_301] :
      ( r2_hidden(k4_filter_0(A_298,C_299,B_300),B_301)
      | ~ r2_hidden(k7_filter_0(A_298,B_300,C_299),B_301)
      | ~ m1_subset_1(k4_filter_0(A_298,C_299,B_300),u1_struct_0(A_298))
      | ~ m1_subset_1(k4_filter_0(A_298,B_300,C_299),u1_struct_0(A_298))
      | ~ v20_lattices(B_301,A_298)
      | ~ v19_lattices(B_301,A_298)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_298)))
      | v1_xboole_0(B_301)
      | ~ l3_lattices(A_298)
      | ~ v10_lattices(A_298)
      | v2_struct_0(A_298)
      | ~ m1_subset_1(C_299,u1_struct_0(A_298))
      | ~ m1_subset_1(B_300,u1_struct_0(A_298))
      | ~ l3_lattices(A_298)
      | ~ v10_lattices(A_298)
      | v2_struct_0(A_298) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_213])).

tff(c_499,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_495])).

tff(c_508,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_128,c_132,c_130,c_499])).

tff(c_509,plain,
    ( ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_471,c_508])).

tff(c_514,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_518,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_514])).

tff(c_524,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_518])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_524])).

tff(c_527,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_531,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_527])).

tff(c_537,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_124,c_126,c_531])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_537])).

tff(c_541,plain,(
    r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_453,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8',k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6',k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_444,c_388])).

tff(c_467,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8',k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6',k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_124,c_379,c_120,c_453])).

tff(c_468,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8',k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6',k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_467])).

tff(c_554,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_6',k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_468])).

tff(c_560,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_554])).

tff(c_567,plain,
    ( v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_124,c_126,c_122,c_541,c_560])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_567])).

tff(c_570,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_8',k3_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_468])).

tff(c_578,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_570])).

tff(c_584,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_120,c_122,c_126,c_578])).

tff(c_585,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_584])).

tff(c_116,plain,(
    r2_hidden(k7_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_623,plain,(
    ! [A_311,C_312,B_313,B_314] :
      ( r2_hidden(k4_filter_0(A_311,C_312,B_313),B_314)
      | ~ r2_hidden(k7_filter_0(A_311,B_313,C_312),B_314)
      | ~ m1_subset_1(k4_filter_0(A_311,C_312,B_313),u1_struct_0(A_311))
      | ~ m1_subset_1(k4_filter_0(A_311,B_313,C_312),u1_struct_0(A_311))
      | ~ v20_lattices(B_314,A_311)
      | ~ v19_lattices(B_314,A_311)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_311)))
      | v1_xboole_0(B_314)
      | ~ l3_lattices(A_311)
      | ~ v10_lattices(A_311)
      | v2_struct_0(A_311)
      | ~ m1_subset_1(C_312,u1_struct_0(A_311))
      | ~ m1_subset_1(B_313,u1_struct_0(A_311))
      | ~ l3_lattices(A_311)
      | ~ v10_lattices(A_311)
      | v2_struct_0(A_311) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_213])).

tff(c_629,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_623])).

tff(c_640,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_128,c_132,c_130,c_629])).

tff(c_641,plain,
    ( ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_585,c_640])).

tff(c_660,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_663,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_660])).

tff(c_669,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_663])).

tff(c_671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_669])).

tff(c_672,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_676,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_672])).

tff(c_682,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_120,c_122,c_676])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_682])).

tff(c_685,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_696,plain,(
    ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_699,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l2_lattices('#skF_3')
    | ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_696])).

tff(c_705,plain,
    ( ~ v4_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_124,c_120,c_699])).

tff(c_706,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_705])).

tff(c_710,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_706])).

tff(c_713,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_140,c_710])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_713])).

tff(c_716,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_720,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),'#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_716])).

tff(c_723,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),'#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_379,c_124,c_120,c_720])).

tff(c_724,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k3_lattices('#skF_3','#skF_5','#skF_7'),'#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_723])).

tff(c_752,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_6'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_724])).

tff(c_765,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_6'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_126,c_124,c_122,c_752])).

tff(c_766,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_6'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_765])).

tff(c_773,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_766])).

tff(c_228,plain,(
    ! [C_245,B_246,A_247,D_248] :
      ( r2_hidden(C_245,B_246)
      | ~ r2_hidden(k4_lattices(A_247,C_245,D_248),B_246)
      | ~ m1_subset_1(D_248,u1_struct_0(A_247))
      | ~ m1_subset_1(C_245,u1_struct_0(A_247))
      | ~ v20_lattices(B_246,A_247)
      | ~ v19_lattices(B_246,A_247)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_247)))
      | v1_xboole_0(B_246)
      | ~ l3_lattices(A_247)
      | ~ v10_lattices(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_797,plain,(
    ! [A_343,B_344,C_345,B_346] :
      ( r2_hidden(k4_filter_0(A_343,B_344,C_345),B_346)
      | ~ r2_hidden(k7_filter_0(A_343,B_344,C_345),B_346)
      | ~ m1_subset_1(k4_filter_0(A_343,C_345,B_344),u1_struct_0(A_343))
      | ~ m1_subset_1(k4_filter_0(A_343,B_344,C_345),u1_struct_0(A_343))
      | ~ v20_lattices(B_346,A_343)
      | ~ v19_lattices(B_346,A_343)
      | ~ m1_subset_1(B_346,k1_zfmisc_1(u1_struct_0(A_343)))
      | v1_xboole_0(B_346)
      | ~ l3_lattices(A_343)
      | ~ v10_lattices(A_343)
      | v2_struct_0(A_343)
      | ~ m1_subset_1(C_345,u1_struct_0(A_343))
      | ~ m1_subset_1(B_344,u1_struct_0(A_343))
      | ~ l3_lattices(A_343)
      | ~ v10_lattices(A_343)
      | v2_struct_0(A_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_801,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_797])).

tff(c_810,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_128,c_132,c_130,c_801])).

tff(c_811,plain,
    ( ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_773,c_810])).

tff(c_816,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_819,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_816])).

tff(c_825,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_819])).

tff(c_827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_825])).

tff(c_828,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_833,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_828])).

tff(c_839,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_124,c_126,c_833])).

tff(c_841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_839])).

tff(c_843,plain,(
    r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_717,plain,(
    m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_755,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7',k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5',k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k3_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_716])).

tff(c_769,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7',k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5',k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_126,c_717,c_122,c_755])).

tff(c_770,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7',k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5',k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_769])).

tff(c_848,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_5',k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_862,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_848])).

tff(c_869,plain,
    ( v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_126,c_124,c_120,c_843,c_862])).

tff(c_871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_869])).

tff(c_872,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_7',k3_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_880,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_872])).

tff(c_886,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_122,c_120,c_124,c_880])).

tff(c_887,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_886])).

tff(c_900,plain,(
    ! [A_357,B_358,C_359,B_360] :
      ( r2_hidden(k4_filter_0(A_357,B_358,C_359),B_360)
      | ~ r2_hidden(k7_filter_0(A_357,B_358,C_359),B_360)
      | ~ m1_subset_1(k4_filter_0(A_357,C_359,B_358),u1_struct_0(A_357))
      | ~ m1_subset_1(k4_filter_0(A_357,B_358,C_359),u1_struct_0(A_357))
      | ~ v20_lattices(B_360,A_357)
      | ~ v19_lattices(B_360,A_357)
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0(A_357)))
      | v1_xboole_0(B_360)
      | ~ l3_lattices(A_357)
      | ~ v10_lattices(A_357)
      | v2_struct_0(A_357)
      | ~ m1_subset_1(C_359,u1_struct_0(A_357))
      | ~ m1_subset_1(B_358,u1_struct_0(A_357))
      | ~ l3_lattices(A_357)
      | ~ v10_lattices(A_357)
      | v2_struct_0(A_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_906,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_900])).

tff(c_917,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_128,c_132,c_130,c_906])).

tff(c_918,plain,
    ( ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_887,c_917])).

tff(c_919,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_918])).

tff(c_922,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_919])).

tff(c_928,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_922])).

tff(c_930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_928])).

tff(c_931,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_954,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_931])).

tff(c_960,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_120,c_122,c_954])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_960])).

tff(c_963,plain,(
    ~ r2_hidden(k7_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_1170,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),k4_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1163,c_963])).

tff(c_1172,plain,(
    ~ m1_subset_1(k4_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1170])).

tff(c_1175,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1172])).

tff(c_1181,plain,
    ( ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_126,c_122,c_1175])).

tff(c_1182,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1181])).

tff(c_1186,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1182])).

tff(c_1189,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_140,c_1186])).

tff(c_1191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1189])).

tff(c_1193,plain,(
    m1_subset_1(k4_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1170])).

tff(c_30,plain,(
    ! [A_19,C_43,B_35,D_47,E_49] :
      ( r2_hidden(k4_filter_0(A_19,k4_lattices(A_19,C_43,E_49),D_47),B_35)
      | ~ r2_hidden(k4_filter_0(A_19,C_43,D_47),B_35)
      | ~ m1_subset_1(E_49,u1_struct_0(A_19))
      | ~ m1_subset_1(D_47,u1_struct_0(A_19))
      | ~ m1_subset_1(C_43,u1_struct_0(A_19))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ v20_lattices(B_35,A_19)
      | ~ v19_lattices(B_35,A_19)
      | v1_xboole_0(B_35)
      | ~ l3_lattices(A_19)
      | ~ v3_filter_0(A_19)
      | ~ v10_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1192,plain,
    ( ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),k4_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1170])).

tff(c_1202,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),k4_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1192])).

tff(c_1208,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1202])).

tff(c_1215,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_124,c_1193,c_120,c_1208])).

tff(c_1216,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_6',k4_lattices('#skF_3','#skF_5','#skF_7')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1215])).

tff(c_1236,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1233,c_1216])).

tff(c_1251,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_124,c_126,c_122,c_1236])).

tff(c_1252,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1251])).

tff(c_1287,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1252])).

tff(c_1359,plain,(
    m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1282])).

tff(c_1019,plain,(
    ! [D_403,B_404,A_405,C_406] :
      ( r2_hidden(D_403,B_404)
      | ~ r2_hidden(k4_lattices(A_405,C_406,D_403),B_404)
      | ~ m1_subset_1(D_403,u1_struct_0(A_405))
      | ~ m1_subset_1(C_406,u1_struct_0(A_405))
      | ~ v20_lattices(B_404,A_405)
      | ~ v19_lattices(B_404,A_405)
      | ~ m1_subset_1(B_404,k1_zfmisc_1(u1_struct_0(A_405)))
      | v1_xboole_0(B_404)
      | ~ l3_lattices(A_405)
      | ~ v10_lattices(A_405)
      | v2_struct_0(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_1378,plain,(
    ! [A_468,C_469,B_470,B_471] :
      ( r2_hidden(k4_filter_0(A_468,C_469,B_470),B_471)
      | ~ r2_hidden(k7_filter_0(A_468,B_470,C_469),B_471)
      | ~ m1_subset_1(k4_filter_0(A_468,C_469,B_470),u1_struct_0(A_468))
      | ~ m1_subset_1(k4_filter_0(A_468,B_470,C_469),u1_struct_0(A_468))
      | ~ v20_lattices(B_471,A_468)
      | ~ v19_lattices(B_471,A_468)
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0(A_468)))
      | v1_xboole_0(B_471)
      | ~ l3_lattices(A_468)
      | ~ v10_lattices(A_468)
      | v2_struct_0(A_468)
      | ~ m1_subset_1(C_469,u1_struct_0(A_468))
      | ~ m1_subset_1(B_470,u1_struct_0(A_468))
      | ~ l3_lattices(A_468)
      | ~ v10_lattices(A_468)
      | v2_struct_0(A_468) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1019])).

tff(c_1384,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_1378])).

tff(c_1397,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_128,c_132,c_130,c_1359,c_1384])).

tff(c_1398,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1287,c_1397])).

tff(c_1408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_1398])).

tff(c_1410,plain,(
    r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_1270,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_1262])).

tff(c_1285,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_128,c_132,c_130,c_1270])).

tff(c_1286,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1285])).

tff(c_1416,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1286])).

tff(c_1419,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1416])).

tff(c_1425,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_1419])).

tff(c_1427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1425])).

tff(c_1428,plain,
    ( ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1286])).

tff(c_1455,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1428])).

tff(c_1458,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1455])).

tff(c_1464,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_120,c_122,c_1458])).

tff(c_1466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1464])).

tff(c_1468,plain,(
    m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1428])).

tff(c_1429,plain,(
    m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1286])).

tff(c_1430,plain,(
    ! [A_472,C_473,B_474,B_475] :
      ( r2_hidden(k4_filter_0(A_472,C_473,B_474),B_475)
      | ~ r2_hidden(k7_filter_0(A_472,B_474,C_473),B_475)
      | ~ m1_subset_1(k4_filter_0(A_472,C_473,B_474),u1_struct_0(A_472))
      | ~ m1_subset_1(k4_filter_0(A_472,B_474,C_473),u1_struct_0(A_472))
      | ~ v20_lattices(B_475,A_472)
      | ~ v19_lattices(B_475,A_472)
      | ~ m1_subset_1(B_475,k1_zfmisc_1(u1_struct_0(A_472)))
      | v1_xboole_0(B_475)
      | ~ l3_lattices(A_472)
      | ~ v10_lattices(A_472)
      | v2_struct_0(A_472)
      | ~ m1_subset_1(C_473,u1_struct_0(A_472))
      | ~ m1_subset_1(B_474,u1_struct_0(A_472))
      | ~ l3_lattices(A_472)
      | ~ v10_lattices(A_472)
      | v2_struct_0(A_472) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1019])).

tff(c_1438,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_1430])).

tff(c_1453,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_128,c_132,c_130,c_1438])).

tff(c_1454,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1453])).

tff(c_1470,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1429,c_1454])).

tff(c_1471,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1470])).

tff(c_1477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_1471])).

tff(c_1478,plain,(
    r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1470])).

tff(c_1242,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_7'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1233,c_1202])).

tff(c_1259,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_7'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_126,c_122,c_1242])).

tff(c_1260,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_7'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1259])).

tff(c_1532,plain,(
    ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1260])).

tff(c_1535,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l1_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1532])).

tff(c_1541,plain,
    ( ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_124,c_120,c_1535])).

tff(c_1542,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1541])).

tff(c_1546,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1542])).

tff(c_1549,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_140,c_1546])).

tff(c_1551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1549])).

tff(c_1552,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1260])).

tff(c_1554,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1552])).

tff(c_1557,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_8','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1554])).

tff(c_1563,plain,
    ( v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_120,c_122,c_124,c_1478,c_1557])).

tff(c_1565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1563])).

tff(c_1566,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_6','#skF_8'),'#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1552])).

tff(c_1577,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1566])).

tff(c_1584,plain,
    ( v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_124,c_126,c_120,c_1410,c_1577])).

tff(c_1586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1584])).

tff(c_1587,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_1598,plain,(
    ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1587])).

tff(c_1601,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l1_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1598])).

tff(c_1607,plain,
    ( ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_124,c_120,c_1601])).

tff(c_1608,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1607])).

tff(c_1612,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1608])).

tff(c_1615,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_140,c_1612])).

tff(c_1617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1615])).

tff(c_1619,plain,(
    m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1587])).

tff(c_1618,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1587])).

tff(c_1625,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_5',k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1618])).

tff(c_1632,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_5',k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_126,c_1619,c_122,c_1625])).

tff(c_1633,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_5',k4_lattices('#skF_3','#skF_6','#skF_8')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1632])).

tff(c_1643,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_8'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1640,c_1633])).

tff(c_1658,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_8'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_126,c_124,c_120,c_1643])).

tff(c_1659,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_8'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1658])).

tff(c_1669,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1659])).

tff(c_1716,plain,(
    ! [A_513,B_514,C_515,B_516] :
      ( r2_hidden(k4_filter_0(A_513,B_514,C_515),B_516)
      | ~ r2_hidden(k7_filter_0(A_513,B_514,C_515),B_516)
      | ~ m1_subset_1(k4_filter_0(A_513,C_515,B_514),u1_struct_0(A_513))
      | ~ m1_subset_1(k4_filter_0(A_513,B_514,C_515),u1_struct_0(A_513))
      | ~ v20_lattices(B_516,A_513)
      | ~ v19_lattices(B_516,A_513)
      | ~ m1_subset_1(B_516,k1_zfmisc_1(u1_struct_0(A_513)))
      | v1_xboole_0(B_516)
      | ~ l3_lattices(A_513)
      | ~ v10_lattices(A_513)
      | v2_struct_0(A_513)
      | ~ m1_subset_1(C_515,u1_struct_0(A_513))
      | ~ m1_subset_1(B_514,u1_struct_0(A_513))
      | ~ l3_lattices(A_513)
      | ~ v10_lattices(A_513)
      | v2_struct_0(A_513) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1051])).

tff(c_1722,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_1716])).

tff(c_1735,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_128,c_132,c_130,c_1722])).

tff(c_1736,plain,
    ( ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1669,c_1735])).

tff(c_1741,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1736])).

tff(c_1744,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1741])).

tff(c_1750,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_126,c_124,c_1744])).

tff(c_1752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1750])).

tff(c_1753,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1736])).

tff(c_1758,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1753])).

tff(c_1764,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_124,c_126,c_1758])).

tff(c_1766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1764])).

tff(c_1768,plain,(
    r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1659])).

tff(c_1649,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),'#skF_8'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),'#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_lattices('#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1640,c_1618])).

tff(c_1666,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),'#skF_8'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),'#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_1193,c_124,c_120,c_1649])).

tff(c_1667,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),'#skF_8'),'#skF_4')
    | ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),'#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1666])).

tff(c_1779,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),'#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1667])).

tff(c_1785,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1779])).

tff(c_1792,plain,
    ( v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_126,c_124,c_122,c_1768,c_1785])).

tff(c_1794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1792])).

tff(c_1795,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3',k4_lattices('#skF_3','#skF_5','#skF_7'),'#skF_8'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1667])).

tff(c_1799,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l3_lattices('#skF_3')
    | ~ v3_filter_0('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1795])).

tff(c_1805,plain,
    ( ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_138,c_136,c_132,c_130,c_128,c_122,c_120,c_126,c_1799])).

tff(c_1806,plain,(
    ~ r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1805])).

tff(c_1815,plain,(
    ! [A_522,B_523,C_524,B_525] :
      ( r2_hidden(k4_filter_0(A_522,B_523,C_524),B_525)
      | ~ r2_hidden(k7_filter_0(A_522,B_523,C_524),B_525)
      | ~ m1_subset_1(k4_filter_0(A_522,C_524,B_523),u1_struct_0(A_522))
      | ~ m1_subset_1(k4_filter_0(A_522,B_523,C_524),u1_struct_0(A_522))
      | ~ v20_lattices(B_525,A_522)
      | ~ v19_lattices(B_525,A_522)
      | ~ m1_subset_1(B_525,k1_zfmisc_1(u1_struct_0(A_522)))
      | v1_xboole_0(B_525)
      | ~ l3_lattices(A_522)
      | ~ v10_lattices(A_522)
      | v2_struct_0(A_522)
      | ~ m1_subset_1(C_524,u1_struct_0(A_522))
      | ~ m1_subset_1(B_523,u1_struct_0(A_522))
      | ~ l3_lattices(A_522)
      | ~ v10_lattices(A_522)
      | v2_struct_0(A_522) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1051])).

tff(c_1823,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | ~ v20_lattices('#skF_4','#skF_3')
    | ~ v19_lattices('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_1815])).

tff(c_1838,plain,
    ( r2_hidden(k4_filter_0('#skF_3','#skF_7','#skF_8'),'#skF_4')
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_128,c_132,c_130,c_1823])).

tff(c_1839,plain,
    ( ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_134,c_1806,c_1838])).

tff(c_1840,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_7','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1839])).

tff(c_1843,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1840])).

tff(c_1849,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_122,c_120,c_1843])).

tff(c_1851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1849])).

tff(c_1852,plain,(
    ~ m1_subset_1(k4_filter_0('#skF_3','#skF_8','#skF_7'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1839])).

tff(c_1856,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1852])).

tff(c_1862,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_136,c_120,c_122,c_1856])).

tff(c_1864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_1862])).

%------------------------------------------------------------------------------
