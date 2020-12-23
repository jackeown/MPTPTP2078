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
% DateTime   : Thu Dec  3 10:27:16 EST 2020

% Result     : Theorem 10.82s
% Output     : CNFRefutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 621 expanded)
%              Number of leaves         :   36 ( 255 expanded)
%              Depth                    :   13
%              Number of atoms          :  315 (4282 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_202,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_46,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_44,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_69,plain,(
    ! [B_135,A_136] :
      ( l1_pre_topc(B_135)
      | ~ m1_pre_topc(B_135,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_81,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_72])).

tff(c_20,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_40,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_122,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( v1_funct_1(k2_tmap_1(A_162,B_163,C_164,D_165))
      | ~ l1_struct_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162),u1_struct_0(B_163))))
      | ~ v1_funct_2(C_164,u1_struct_0(A_162),u1_struct_0(B_163))
      | ~ v1_funct_1(C_164)
      | ~ l1_struct_0(B_163)
      | ~ l1_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_130,plain,(
    ! [D_165] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6',D_165))
      | ~ l1_struct_0(D_165)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_122])).

tff(c_137,plain,(
    ! [D_165] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6',D_165))
      | ~ l1_struct_0(D_165)
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_130])).

tff(c_138,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_155,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_138])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_155])).

tff(c_161,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_160,plain,(
    ! [D_165] :
      ( ~ l1_struct_0('#skF_3')
      | v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6',D_165))
      | ~ l1_struct_0(D_165) ) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_162,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_165,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_162])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_165])).

tff(c_171,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_221,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( m1_subset_1(k2_tmap_1(A_191,B_192,C_193,D_194),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_194),u1_struct_0(B_192))))
      | ~ l1_struct_0(D_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),u1_struct_0(B_192))))
      | ~ v1_funct_2(C_193,u1_struct_0(A_191),u1_struct_0(B_192))
      | ~ v1_funct_1(C_193)
      | ~ l1_struct_0(B_192)
      | ~ l1_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8,plain,(
    ! [A_5,B_6] : v1_funct_1('#skF_1'(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_funct_2('#skF_1'(A_5,B_6),A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_5,B_6] : m1_subset_1('#skF_1'(A_5,B_6),k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_174,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( r2_funct_2(A_174,B_175,C_176,C_176)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_2(D_177,A_174,B_175)
      | ~ v1_funct_1(D_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_2(C_176,A_174,B_175)
      | ~ v1_funct_1(C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_178,plain,(
    ! [A_5,B_6,C_176] :
      ( r2_funct_2(A_5,B_6,C_176,C_176)
      | ~ v1_funct_2('#skF_1'(A_5,B_6),A_5,B_6)
      | ~ v1_funct_1('#skF_1'(A_5,B_6))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_176,A_5,B_6)
      | ~ v1_funct_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_184,plain,(
    ! [A_5,B_6,C_176] :
      ( r2_funct_2(A_5,B_6,C_176,C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_176,A_5,B_6)
      | ~ v1_funct_1(C_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_178])).

tff(c_611,plain,(
    ! [D_314,B_315,A_316,C_317] :
      ( r2_funct_2(u1_struct_0(D_314),u1_struct_0(B_315),k2_tmap_1(A_316,B_315,C_317,D_314),k2_tmap_1(A_316,B_315,C_317,D_314))
      | ~ v1_funct_2(k2_tmap_1(A_316,B_315,C_317,D_314),u1_struct_0(D_314),u1_struct_0(B_315))
      | ~ v1_funct_1(k2_tmap_1(A_316,B_315,C_317,D_314))
      | ~ l1_struct_0(D_314)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_316),u1_struct_0(B_315))))
      | ~ v1_funct_2(C_317,u1_struct_0(A_316),u1_struct_0(B_315))
      | ~ v1_funct_1(C_317)
      | ~ l1_struct_0(B_315)
      | ~ l1_struct_0(A_316) ) ),
    inference(resolution,[status(thm)],[c_221,c_184])).

tff(c_32,plain,(
    ! [A_35,F_97,B_67,E_95,D_91,C_83] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0(B_67),k3_tmap_1(A_35,B_67,C_83,D_91,F_97),k2_tmap_1(A_35,B_67,E_95,D_91))
      | ~ m1_pre_topc(D_91,C_83)
      | ~ r2_funct_2(u1_struct_0(C_83),u1_struct_0(B_67),F_97,k2_tmap_1(A_35,B_67,E_95,C_83))
      | ~ m1_subset_1(F_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_83),u1_struct_0(B_67))))
      | ~ v1_funct_2(F_97,u1_struct_0(C_83),u1_struct_0(B_67))
      | ~ v1_funct_1(F_97)
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35),u1_struct_0(B_67))))
      | ~ v1_funct_2(E_95,u1_struct_0(A_35),u1_struct_0(B_67))
      | ~ v1_funct_1(E_95)
      | ~ m1_pre_topc(D_91,A_35)
      | v2_struct_0(D_91)
      | ~ m1_pre_topc(C_83,A_35)
      | v2_struct_0(C_83)
      | ~ l1_pre_topc(B_67)
      | ~ v2_pre_topc(B_67)
      | v2_struct_0(B_67)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_5129,plain,(
    ! [C_934,D_932,A_935,B_931,D_933] :
      ( r2_funct_2(u1_struct_0(D_932),u1_struct_0(B_931),k3_tmap_1(A_935,B_931,D_933,D_932,k2_tmap_1(A_935,B_931,C_934,D_933)),k2_tmap_1(A_935,B_931,C_934,D_932))
      | ~ m1_pre_topc(D_932,D_933)
      | ~ m1_subset_1(k2_tmap_1(A_935,B_931,C_934,D_933),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_933),u1_struct_0(B_931))))
      | ~ m1_pre_topc(D_932,A_935)
      | v2_struct_0(D_932)
      | ~ m1_pre_topc(D_933,A_935)
      | v2_struct_0(D_933)
      | ~ l1_pre_topc(B_931)
      | ~ v2_pre_topc(B_931)
      | v2_struct_0(B_931)
      | ~ l1_pre_topc(A_935)
      | ~ v2_pre_topc(A_935)
      | v2_struct_0(A_935)
      | ~ v1_funct_2(k2_tmap_1(A_935,B_931,C_934,D_933),u1_struct_0(D_933),u1_struct_0(B_931))
      | ~ v1_funct_1(k2_tmap_1(A_935,B_931,C_934,D_933))
      | ~ l1_struct_0(D_933)
      | ~ m1_subset_1(C_934,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_935),u1_struct_0(B_931))))
      | ~ v1_funct_2(C_934,u1_struct_0(A_935),u1_struct_0(B_931))
      | ~ v1_funct_1(C_934)
      | ~ l1_struct_0(B_931)
      | ~ l1_struct_0(A_935) ) ),
    inference(resolution,[status(thm)],[c_611,c_32])).

tff(c_34,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4',k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_5134,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_5129,c_34])).

tff(c_5168,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_171,c_42,c_40,c_38,c_60,c_58,c_54,c_52,c_44,c_48,c_36,c_5134])).

tff(c_5169,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_46,c_50,c_5168])).

tff(c_5198,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5169])).

tff(c_5201,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_5198])).

tff(c_5205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_5201])).

tff(c_5207,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_5169])).

tff(c_202,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( v1_funct_2(k2_tmap_1(A_181,B_182,C_183,D_184),u1_struct_0(D_184),u1_struct_0(B_182))
      | ~ l1_struct_0(D_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0(B_182))))
      | ~ v1_funct_2(C_183,u1_struct_0(A_181),u1_struct_0(B_182))
      | ~ v1_funct_1(C_183)
      | ~ l1_struct_0(B_182)
      | ~ l1_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_210,plain,(
    ! [D_184] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6',D_184),u1_struct_0(D_184),u1_struct_0('#skF_3'))
      | ~ l1_struct_0(D_184)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_202])).

tff(c_217,plain,(
    ! [D_184] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6',D_184),u1_struct_0(D_184),u1_struct_0('#skF_3'))
      | ~ l1_struct_0(D_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_171,c_42,c_40,c_210])).

tff(c_239,plain,(
    ! [A_205,B_206,C_207,D_208] :
      ( k2_partfun1(u1_struct_0(A_205),u1_struct_0(B_206),C_207,u1_struct_0(D_208)) = k2_tmap_1(A_205,B_206,C_207,D_208)
      | ~ m1_pre_topc(D_208,A_205)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_205),u1_struct_0(B_206))))
      | ~ v1_funct_2(C_207,u1_struct_0(A_205),u1_struct_0(B_206))
      | ~ v1_funct_1(C_207)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_249,plain,(
    ! [D_208] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_208)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_208)
      | ~ m1_pre_topc(D_208,'#skF_2')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_239])).

tff(c_257,plain,(
    ! [D_208] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_208)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_208)
      | ~ m1_pre_topc(D_208,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_42,c_40,c_249])).

tff(c_259,plain,(
    ! [D_209] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_209)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_209)
      | ~ m1_pre_topc(D_209,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_257])).

tff(c_89,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( v1_funct_1(k2_partfun1(A_139,B_140,C_141,D_142))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [D_142] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',D_142))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_99,plain,(
    ! [D_142] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',D_142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_93])).

tff(c_278,plain,(
    ! [D_209] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6',D_209))
      | ~ m1_pre_topc(D_209,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_99])).

tff(c_26,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( m1_subset_1(k2_tmap_1(A_31,B_32,C_33,D_34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_34),u1_struct_0(B_32))))
      | ~ l1_struct_0(D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31),u1_struct_0(B_32))))
      | ~ v1_funct_2(C_33,u1_struct_0(A_31),u1_struct_0(B_32))
      | ~ v1_funct_1(C_33)
      | ~ l1_struct_0(B_32)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5206,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_5169])).

tff(c_5410,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_5206])).

tff(c_5413,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_5410])).

tff(c_5417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_171,c_42,c_40,c_38,c_5207,c_5413])).

tff(c_5418,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5206])).

tff(c_5456,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5418])).

tff(c_5459,plain,(
    ~ m1_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_278,c_5456])).

tff(c_5466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5459])).

tff(c_5467,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5418])).

tff(c_5603,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_217,c_5467])).

tff(c_5607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5207,c_5603])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:51:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.82/4.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.28  
% 10.82/4.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.28  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.82/4.28  
% 10.82/4.28  %Foreground sorts:
% 10.82/4.28  
% 10.82/4.28  
% 10.82/4.28  %Background operators:
% 10.82/4.28  
% 10.82/4.28  
% 10.82/4.28  %Foreground operators:
% 10.82/4.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.82/4.28  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 10.82/4.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.82/4.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.82/4.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.82/4.28  tff('#skF_5', type, '#skF_5': $i).
% 10.82/4.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.82/4.28  tff('#skF_6', type, '#skF_6': $i).
% 10.82/4.28  tff('#skF_2', type, '#skF_2': $i).
% 10.82/4.28  tff('#skF_3', type, '#skF_3': $i).
% 10.82/4.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.82/4.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.82/4.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.82/4.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.82/4.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.82/4.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.82/4.28  tff('#skF_4', type, '#skF_4': $i).
% 10.82/4.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.82/4.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.82/4.28  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.82/4.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.82/4.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.82/4.28  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 10.82/4.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.82/4.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.82/4.28  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 10.82/4.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.82/4.28  
% 10.93/4.30  tff(f_202, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 10.93/4.30  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.93/4.30  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.93/4.30  tff(f_116, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 10.93/4.30  tff(f_46, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 10.93/4.30  tff(f_60, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 10.93/4.30  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 10.93/4.30  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 10.93/4.30  tff(f_33, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 10.93/4.30  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_44, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_69, plain, (![B_135, A_136]: (l1_pre_topc(B_135) | ~m1_pre_topc(B_135, A_136) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.93/4.30  tff(c_72, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_69])).
% 10.93/4.30  tff(c_81, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_72])).
% 10.93/4.30  tff(c_20, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.93/4.30  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_40, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_122, plain, (![A_162, B_163, C_164, D_165]: (v1_funct_1(k2_tmap_1(A_162, B_163, C_164, D_165)) | ~l1_struct_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162), u1_struct_0(B_163)))) | ~v1_funct_2(C_164, u1_struct_0(A_162), u1_struct_0(B_163)) | ~v1_funct_1(C_164) | ~l1_struct_0(B_163) | ~l1_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.93/4.30  tff(c_130, plain, (![D_165]: (v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_165)) | ~l1_struct_0(D_165) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_122])).
% 10.93/4.30  tff(c_137, plain, (![D_165]: (v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_165)) | ~l1_struct_0(D_165) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_130])).
% 10.93/4.30  tff(c_138, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_137])).
% 10.93/4.30  tff(c_155, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_138])).
% 10.93/4.30  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_155])).
% 10.93/4.30  tff(c_161, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_137])).
% 10.93/4.30  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_160, plain, (![D_165]: (~l1_struct_0('#skF_3') | v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_165)) | ~l1_struct_0(D_165))), inference(splitRight, [status(thm)], [c_137])).
% 10.93/4.30  tff(c_162, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_160])).
% 10.93/4.30  tff(c_165, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_162])).
% 10.93/4.30  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_165])).
% 10.93/4.30  tff(c_171, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_160])).
% 10.93/4.30  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_221, plain, (![A_191, B_192, C_193, D_194]: (m1_subset_1(k2_tmap_1(A_191, B_192, C_193, D_194), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_194), u1_struct_0(B_192)))) | ~l1_struct_0(D_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), u1_struct_0(B_192)))) | ~v1_funct_2(C_193, u1_struct_0(A_191), u1_struct_0(B_192)) | ~v1_funct_1(C_193) | ~l1_struct_0(B_192) | ~l1_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.93/4.30  tff(c_8, plain, (![A_5, B_6]: (v1_funct_1('#skF_1'(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.93/4.30  tff(c_6, plain, (![A_5, B_6]: (v1_funct_2('#skF_1'(A_5, B_6), A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.93/4.30  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1('#skF_1'(A_5, B_6), k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.93/4.30  tff(c_174, plain, (![A_174, B_175, C_176, D_177]: (r2_funct_2(A_174, B_175, C_176, C_176) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_2(D_177, A_174, B_175) | ~v1_funct_1(D_177) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_2(C_176, A_174, B_175) | ~v1_funct_1(C_176))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.93/4.30  tff(c_178, plain, (![A_5, B_6, C_176]: (r2_funct_2(A_5, B_6, C_176, C_176) | ~v1_funct_2('#skF_1'(A_5, B_6), A_5, B_6) | ~v1_funct_1('#skF_1'(A_5, B_6)) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(C_176, A_5, B_6) | ~v1_funct_1(C_176))), inference(resolution, [status(thm)], [c_16, c_174])).
% 10.93/4.30  tff(c_184, plain, (![A_5, B_6, C_176]: (r2_funct_2(A_5, B_6, C_176, C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(C_176, A_5, B_6) | ~v1_funct_1(C_176))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6, c_178])).
% 10.93/4.30  tff(c_611, plain, (![D_314, B_315, A_316, C_317]: (r2_funct_2(u1_struct_0(D_314), u1_struct_0(B_315), k2_tmap_1(A_316, B_315, C_317, D_314), k2_tmap_1(A_316, B_315, C_317, D_314)) | ~v1_funct_2(k2_tmap_1(A_316, B_315, C_317, D_314), u1_struct_0(D_314), u1_struct_0(B_315)) | ~v1_funct_1(k2_tmap_1(A_316, B_315, C_317, D_314)) | ~l1_struct_0(D_314) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_316), u1_struct_0(B_315)))) | ~v1_funct_2(C_317, u1_struct_0(A_316), u1_struct_0(B_315)) | ~v1_funct_1(C_317) | ~l1_struct_0(B_315) | ~l1_struct_0(A_316))), inference(resolution, [status(thm)], [c_221, c_184])).
% 10.93/4.30  tff(c_32, plain, (![A_35, F_97, B_67, E_95, D_91, C_83]: (r2_funct_2(u1_struct_0(D_91), u1_struct_0(B_67), k3_tmap_1(A_35, B_67, C_83, D_91, F_97), k2_tmap_1(A_35, B_67, E_95, D_91)) | ~m1_pre_topc(D_91, C_83) | ~r2_funct_2(u1_struct_0(C_83), u1_struct_0(B_67), F_97, k2_tmap_1(A_35, B_67, E_95, C_83)) | ~m1_subset_1(F_97, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_83), u1_struct_0(B_67)))) | ~v1_funct_2(F_97, u1_struct_0(C_83), u1_struct_0(B_67)) | ~v1_funct_1(F_97) | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35), u1_struct_0(B_67)))) | ~v1_funct_2(E_95, u1_struct_0(A_35), u1_struct_0(B_67)) | ~v1_funct_1(E_95) | ~m1_pre_topc(D_91, A_35) | v2_struct_0(D_91) | ~m1_pre_topc(C_83, A_35) | v2_struct_0(C_83) | ~l1_pre_topc(B_67) | ~v2_pre_topc(B_67) | v2_struct_0(B_67) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_163])).
% 10.93/4.30  tff(c_5129, plain, (![C_934, D_932, A_935, B_931, D_933]: (r2_funct_2(u1_struct_0(D_932), u1_struct_0(B_931), k3_tmap_1(A_935, B_931, D_933, D_932, k2_tmap_1(A_935, B_931, C_934, D_933)), k2_tmap_1(A_935, B_931, C_934, D_932)) | ~m1_pre_topc(D_932, D_933) | ~m1_subset_1(k2_tmap_1(A_935, B_931, C_934, D_933), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_933), u1_struct_0(B_931)))) | ~m1_pre_topc(D_932, A_935) | v2_struct_0(D_932) | ~m1_pre_topc(D_933, A_935) | v2_struct_0(D_933) | ~l1_pre_topc(B_931) | ~v2_pre_topc(B_931) | v2_struct_0(B_931) | ~l1_pre_topc(A_935) | ~v2_pre_topc(A_935) | v2_struct_0(A_935) | ~v1_funct_2(k2_tmap_1(A_935, B_931, C_934, D_933), u1_struct_0(D_933), u1_struct_0(B_931)) | ~v1_funct_1(k2_tmap_1(A_935, B_931, C_934, D_933)) | ~l1_struct_0(D_933) | ~m1_subset_1(C_934, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_935), u1_struct_0(B_931)))) | ~v1_funct_2(C_934, u1_struct_0(A_935), u1_struct_0(B_931)) | ~v1_funct_1(C_934) | ~l1_struct_0(B_931) | ~l1_struct_0(A_935))), inference(resolution, [status(thm)], [c_611, c_32])).
% 10.93/4.30  tff(c_34, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.93/4.30  tff(c_5134, plain, (~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')) | ~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_5129, c_34])).
% 10.93/4.30  tff(c_5168, plain, (~m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')) | ~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_171, c_42, c_40, c_38, c_60, c_58, c_54, c_52, c_44, c_48, c_36, c_5134])).
% 10.93/4.30  tff(c_5169, plain, (~m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_46, c_50, c_5168])).
% 10.93/4.30  tff(c_5198, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_5169])).
% 10.93/4.30  tff(c_5201, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_5198])).
% 10.93/4.30  tff(c_5205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_5201])).
% 10.93/4.30  tff(c_5207, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_5169])).
% 10.93/4.30  tff(c_202, plain, (![A_181, B_182, C_183, D_184]: (v1_funct_2(k2_tmap_1(A_181, B_182, C_183, D_184), u1_struct_0(D_184), u1_struct_0(B_182)) | ~l1_struct_0(D_184) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), u1_struct_0(B_182)))) | ~v1_funct_2(C_183, u1_struct_0(A_181), u1_struct_0(B_182)) | ~v1_funct_1(C_183) | ~l1_struct_0(B_182) | ~l1_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.93/4.30  tff(c_210, plain, (![D_184]: (v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_184), u1_struct_0(D_184), u1_struct_0('#skF_3')) | ~l1_struct_0(D_184) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_202])).
% 10.93/4.30  tff(c_217, plain, (![D_184]: (v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_184), u1_struct_0(D_184), u1_struct_0('#skF_3')) | ~l1_struct_0(D_184))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_171, c_42, c_40, c_210])).
% 10.93/4.30  tff(c_239, plain, (![A_205, B_206, C_207, D_208]: (k2_partfun1(u1_struct_0(A_205), u1_struct_0(B_206), C_207, u1_struct_0(D_208))=k2_tmap_1(A_205, B_206, C_207, D_208) | ~m1_pre_topc(D_208, A_205) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_205), u1_struct_0(B_206)))) | ~v1_funct_2(C_207, u1_struct_0(A_205), u1_struct_0(B_206)) | ~v1_funct_1(C_207) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.93/4.30  tff(c_249, plain, (![D_208]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_208))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_208) | ~m1_pre_topc(D_208, '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_239])).
% 10.93/4.30  tff(c_257, plain, (![D_208]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_208))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_208) | ~m1_pre_topc(D_208, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_42, c_40, c_249])).
% 10.93/4.30  tff(c_259, plain, (![D_209]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_209))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_209) | ~m1_pre_topc(D_209, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_257])).
% 10.93/4.30  tff(c_89, plain, (![A_139, B_140, C_141, D_142]: (v1_funct_1(k2_partfun1(A_139, B_140, C_141, D_142)) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_1(C_141))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.93/4.30  tff(c_93, plain, (![D_142]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', D_142)) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_89])).
% 10.93/4.30  tff(c_99, plain, (![D_142]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', D_142)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_93])).
% 10.93/4.30  tff(c_278, plain, (![D_209]: (v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_209)) | ~m1_pre_topc(D_209, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_99])).
% 10.93/4.30  tff(c_26, plain, (![A_31, B_32, C_33, D_34]: (m1_subset_1(k2_tmap_1(A_31, B_32, C_33, D_34), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_34), u1_struct_0(B_32)))) | ~l1_struct_0(D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31), u1_struct_0(B_32)))) | ~v1_funct_2(C_33, u1_struct_0(A_31), u1_struct_0(B_32)) | ~v1_funct_1(C_33) | ~l1_struct_0(B_32) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.93/4.30  tff(c_5206, plain, (~v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')) | ~v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_5169])).
% 10.93/4.30  tff(c_5410, plain, (~m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_5206])).
% 10.93/4.30  tff(c_5413, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_5410])).
% 10.93/4.30  tff(c_5417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_171, c_42, c_40, c_38, c_5207, c_5413])).
% 10.93/4.30  tff(c_5418, plain, (~v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_5206])).
% 10.93/4.30  tff(c_5456, plain, (~v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_5418])).
% 10.93/4.30  tff(c_5459, plain, (~m1_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_278, c_5456])).
% 10.93/4.30  tff(c_5466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_5459])).
% 10.93/4.30  tff(c_5467, plain, (~v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_5418])).
% 10.93/4.30  tff(c_5603, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_217, c_5467])).
% 10.93/4.30  tff(c_5607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5207, c_5603])).
% 10.93/4.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.30  
% 10.93/4.30  Inference rules
% 10.93/4.30  ----------------------
% 10.93/4.30  #Ref     : 0
% 10.93/4.30  #Sup     : 1171
% 10.93/4.30  #Fact    : 0
% 10.93/4.30  #Define  : 0
% 10.93/4.30  #Split   : 6
% 10.93/4.30  #Chain   : 0
% 10.93/4.30  #Close   : 0
% 10.93/4.30  
% 10.93/4.30  Ordering : KBO
% 10.93/4.30  
% 10.93/4.30  Simplification rules
% 10.93/4.30  ----------------------
% 10.93/4.30  #Subsume      : 352
% 10.93/4.30  #Demod        : 2258
% 10.93/4.30  #Tautology    : 69
% 10.93/4.30  #SimpNegUnit  : 327
% 10.93/4.30  #BackRed      : 0
% 10.93/4.30  
% 10.93/4.30  #Partial instantiations: 0
% 10.93/4.30  #Strategies tried      : 1
% 10.93/4.30  
% 10.93/4.30  Timing (in seconds)
% 10.93/4.30  ----------------------
% 10.93/4.30  Preprocessing        : 0.36
% 10.93/4.30  Parsing              : 0.20
% 10.93/4.30  CNF conversion       : 0.04
% 10.93/4.30  Main loop            : 3.18
% 10.93/4.30  Inferencing          : 0.90
% 10.93/4.30  Reduction            : 0.90
% 10.93/4.30  Demodulation         : 0.70
% 10.93/4.30  BG Simplification    : 0.08
% 10.93/4.30  Subsumption          : 1.21
% 10.93/4.30  Abstraction          : 0.13
% 10.93/4.30  MUC search           : 0.00
% 10.93/4.30  Cooper               : 0.00
% 10.93/4.30  Total                : 3.57
% 10.93/4.30  Index Insertion      : 0.00
% 10.93/4.30  Index Deletion       : 0.00
% 10.93/4.30  Index Matching       : 0.00
% 10.93/4.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
